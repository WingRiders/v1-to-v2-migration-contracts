use aiken/builtin
use aiken/hash.{Blake2b_224, Hash}
use aiken/list
use aiken/time.{PosixTime}
use aiken/transaction.{Datum, InlineDatum, Output, ScriptContext, Spend}
use aiken/transaction/credential.{
  Address, Script, ScriptCredential, VerificationKey, VerificationKeyCredential,
}
use aiken/transaction/value.{AssetName, PolicyId}

type MigrationRedeemer {
  Emergency
  Migrate
}

type AssetClass {
  currency_symbol: PolicyId,
  token_name: AssetName,
}

type ShareLockDatum {
  owner: Address,
  preferred_stake_pool: Hash<Blake2b_224, VerificationKey>,
  farming_share_token_class: AssetClass,
}

// We get an unused constructor warning here,
// which is expected, but we need to align with what the request datum is
type DatumType {
  No
  Hash
  Inline
}

type RequestDatum {
  oil: Int,
  beneficiary: Address,
  owner: Address,
  compensation_datum: Data,
  compensation_datum_type: DatumType,
  deadline: PosixTime,
  asset_a_symbol: PolicyId,
  asset_a_token: AssetName,
  asset_b_symbol: PolicyId,
  asset_b_token: AssetName,
  action: Data,
  a_scale: Int,
  b_scale: Int,
}

validator(
  agent_key: Hash<Blake2b_224, VerificationKey>,
  user_key: Hash<Blake2b_224, VerificationKey>,
  constant_product_request_script_hash: Hash<Blake2b_224, Script>,
  stableswap_request_script_hash: Hash<Blake2b_224, Script>,
  shares_lock_script_hash: Hash<Blake2b_224, Script>,
) {
  fn migrate(
    _datum: Data,
    redeemer: MigrationRedeemer,
    context: ScriptContext,
  ) -> Bool {
    expect ScriptContext { transaction, purpose: Spend(own_ref) } = context
    expect Some(own_input) =
      list.find(transaction.inputs, fn(i) { i.output_reference == own_ref })
    let own_address = own_input.output.address
    when redeemer is {
      Emergency -> list.has(transaction.extra_signatories, user_key)?
      Migrate -> {
        let inputs_first = builtin.head_list(transaction.inputs)
        let inputs_second =
          builtin.head_list(builtin.tail_list(transaction.inputs))

        // The first/second input must be a migration script, all validation is delegated to it
        if
        inputs_first.output_reference != own_ref && inputs_second.output_reference != own_ref{
        
          let inputs_first_script = inputs_first.output.address
          let inputs_second_script = inputs_second.output.address
          when inputs_first_script.payment_credential is {
            ScriptCredential(_) ->
              if inputs_first_script == own_address {
                True
              } else {
                when inputs_second_script.payment_credential is {
                  ScriptCredential(_) -> (inputs_second_script == own_address)?
                  _ -> False?
                }
              }
            _ ->
              when inputs_second_script.payment_credential is {
                ScriptCredential(_) -> (inputs_second_script == own_address)?
                _ -> False?
              }
          }
        } else {
          // Here starts the main validation
          let inputs_scripts_count =
            list.count(
              transaction.inputs,
              fn(input) {
                when input.output.address.payment_credential is {
                  ScriptCredential(..) -> True
                  _ -> False
                }
              },
            )
          let inputs_migrations_count =
            list.count(
              transaction.inputs,
              fn(input) { input.output.address == own_address },
            )
          let outputs_scripts_count =
            list.count(
              transaction.outputs,
              fn(output) {
                when output.address.payment_credential is {
                  ScriptCredential(..) -> True
                  _ -> False
                }
              },
            )

          and {
            // There are only migrations of the user + 1 oil provider script
            (inputs_scripts_count == inputs_migrations_count + 1)?,
            // There are as many requests as there are migration inputs
            (inputs_migrations_count == outputs_scripts_count)?,
            // Each request has the user as an owner, and the beneficiary is correct;
            // The change goes to the user
            parse_requests_and_change(
              user_key,
              constant_product_request_script_hash,
              stableswap_request_script_hash,
              shares_lock_script_hash,
              transaction.outputs,
            )?,
            // Only the migration agent can apply the migrations
            list.has(transaction.extra_signatories, agent_key)?,
          }
        }
      }
    }
  }
}

fn is_address_with_script_hash(
  address: Address,
  script_hash: Hash<Blake2b_224, Script>,
) -> Bool {
  when address.payment_credential is {
    ScriptCredential(hash) -> script_hash == hash
    VerificationKeyCredential(_) -> False
  }
}

fn parse_requests_and_change(
  user_key: Hash<Blake2b_224, VerificationKey>,
  constant_product_request_script_hash: Hash<Blake2b_224, Script>,
  stableswap_request_script_hash: Hash<Blake2b_224, Script>,
  shares_lock_script_hash: Hash<Blake2b_224, Script>,
  outputs: List<Output>,
) -> Bool {
  when outputs is {
    [] -> True
    [output, ..rest] ->
      if
      !is_address_with_script_hash(
        output.address,
        constant_product_request_script_hash,
      ) && !is_address_with_script_hash(
        output.address,
        stableswap_request_script_hash,
      ){
      
        // This is the change output
        expect VerificationKeyCredential(change_output_key) =
          output.address.payment_credential
        and {
          (change_output_key == user_key)?,
          parse_requests_and_change(
            user_key,
            constant_product_request_script_hash,
            stableswap_request_script_hash,
            shares_lock_script_hash,
            rest,
          ),
        }
      } else {
        // NOTE: requests must have datums inline
        expect request_datum: RequestDatum = try_inline_datum(output.datum)
        expect VerificationKeyCredential(request_owner_key) =
          request_datum.owner.payment_credential

        let beneficiary_correct =
          when request_datum.beneficiary.payment_credential is {
            VerificationKeyCredential(request_beneficiary_key) -> and {
                // We expect no compensation datum for regular requests
                (request_datum.compensation_datum_type == No)?,
                // We enforce compensation datum == [] to prevent
                // the agent from setting it to a huge blob
                // preventing the request from being applied
                (request_datum.compensation_datum == builtin.list_data([]))?,
                (request_beneficiary_key == user_key)?,
              }
            ScriptCredential(request_beneficiary_script_hash) -> {
              expect compensation_datum: ShareLockDatum =
                request_datum.compensation_datum
              and {
                // We expect a hash compensation datum for shares lock requests
                // since the shares lock contract is V1
                (request_datum.compensation_datum_type == Hash)?,
                (request_beneficiary_script_hash == shares_lock_script_hash)?,
                when compensation_datum.owner.payment_credential is {
                  VerificationKeyCredential(shares_lock_key) ->
                    (shares_lock_key == user_key)?
                  _ -> False?
                },
              }
            }
          }
        and {
          (request_owner_key == user_key)?,
          beneficiary_correct?,
          parse_requests_and_change(
            user_key,
            constant_product_request_script_hash,
            stableswap_request_script_hash,
            shares_lock_script_hash,
            rest,
          ),
        }
      }
  }
}

fn try_inline_datum(a: Datum) -> Data {
  when a is {
    InlineDatum(d) -> d
    _ -> fail
  }
}

use aiken/hash.{Blake2b_224, Hash}
use aiken/interval.{Finite}
use aiken/list
use aiken/time.{PosixTime}
use aiken/transaction.{ScriptContext, Spend}
use aiken/transaction/credential.{
  Address, VerificationKey, VerificationKeyCredential,
}

type OilHolderDatum {
  owner: Address,
  timeout: PosixTime,
}

validator(agent_key: Hash<Blake2b_224, VerificationKey>) {
  fn use_up(
    datum: OilHolderDatum,
    _redeemer: Data,
    context: ScriptContext,
  ) -> Bool {
    let OilHolderDatum(owner, timeout) = datum
    expect VerificationKeyCredential(owner_key) = owner.payment_credential
    expect ScriptContext { transaction, purpose: Spend(_) } = context
    or {
      // Normal path: migration application
      list.has(transaction.extra_signatories, agent_key)?,
      // Emergency path: user can claim the funds back
      {
        expect Finite(current_time) =
          transaction.validity_range.lower_bound.bound_type
        and {
          (current_time > timeout)?,
          list.has(transaction.extra_signatories, owner_key)?,
        }
      },
    }
  }
}

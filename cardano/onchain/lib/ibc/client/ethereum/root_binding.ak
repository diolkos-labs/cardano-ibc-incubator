use aiken/builtin
use aiken/collection/pairs
use cardano/transaction.{Mint, Transaction}
use ibc/utils/validator_utils

// The actual minting policy decodes and validates the complete RootAction.
// HostState needs only its operation and deployment identities. Decoding the
// large witness lists here again needlessly increases the reference-script size.
pub fn require_proof(tx: Transaction, root_policy: ByteArray, host_policy: ByteArray,
  client_policy: ByteArray, operation: Int) -> Bool {
  expect validator_utils.require_exact_marker_mint(tx.mint, root_policy, #"", 1)
  expect Some(data) = pairs.get_first(tx.redeemers, Mint(root_policy))
  let Pair(tag, fields) = builtin.un_constr_data(data)
  expect [host, client, .._] = fields
  and {
    tag == operation,
    builtin.un_b_data(host) == host_policy,
    builtin.un_b_data(client) == client_policy,
  }
}

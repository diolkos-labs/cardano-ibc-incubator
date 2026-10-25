// IBC State Commitment (Merkle Root) Helpers
//
// This module defines a deterministic way to update `ibc_state_root` on-chain.
//
// Why this exists
// - The HostState UTxO datum contains `ibc_state_root`, which is the commitment
//   a counterparty will use to verify proofs about Cardano's IBC state.
// - If validators accept any new root without checking how it was derived, an
//   operator could commit an arbitrary root and then produce "proofs" against
//   that arbitrary root.
//
// What we enforce
// - Each HostState update transaction carries a small "update witness" per key.
// - The witness is the list of sibling hashes along the key's path in the tree.
// - With those siblings, a validator can recompute:
//   1) the old root (using the old value)
//   2) the new root (using the new value)
// - The transaction only passes if the recomputed new root equals the root
//   written into the new HostState datum.
//
// Important implementation choices
// - SHA-256 is used everywhere.
// - Keys are hashed with SHA-256 and the first `merkle_depth_bits` bits define
//   the left/right directions from leaf to root.
// - Non-empty leaves commit to both `sha256(key)` and `sha256(value)`, while
//   empty values remain the all-zero sparse-tree leaf.
// - The "empty value" is represented by an empty bytearray, which produces a
//   well-defined default leaf digest via SHA-256.

use aiken/builtin
use aiken/collection/list
use aiken/fuzz
use aiken/primitive/bytearray
use ibc/utils/bits

/// Number of bits taken from `sha256(key)` to define the path.
///
/// This is a trade-off:
/// - More bits => lower collision risk, larger witnesses and higher script cost
/// - Fewer bits => smaller witnesses, higher collision risk
///
/// 64 bits is a pragmatic starting point for production-style testing.
pub const merkle_depth_bits: Int = 64

/// Hash size used throughout the commitment scheme (SHA-256).
pub const hash_size_bytes: Int = 32

/// The 32-byte "all zeros" hash.
///
/// We use this as the commitment for an entirely empty subtree.
pub const empty_hash: ByteArray =
  #"0000000000000000000000000000000000000000000000000000000000000000"

/// SHA-256 of the empty bytearray.
///
/// This is a stable constant used to detect the "default / absent" value.
pub const empty_value_hash: ByteArray =
  #"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"

/// Hash the raw value bytes.
///
/// We hash values before placing them in the Merkle tree so that:
/// - leaves always commit to a fixed-size 32-byte digest
/// - the rest of the tree never depends on variable-length concatenations
pub fn value_hash(value: ByteArray) -> ByteArray {
  builtin.sha2_256(value)
}

/// Hash a leaf from a key digest and value digest.
///
/// Non-empty leaf hash = sha256(0x00 || key_hash || value_hash)
pub fn leaf_hash(key_hash: ByteArray, value_hash: ByteArray) -> ByteArray {
  expect bytearray.length(key_hash) == hash_size_bytes
  expect bytearray.length(value_hash) == hash_size_bytes
  // Special-case the default / absent value:
  //
  // - When the committed value is "empty", we treat the leaf as the all-zeros hash.
  // - This makes the empty tree root also be the all-zeros hash, which matches the
  //   existing `empty_ibc_state_root` used throughout the codebase today.
  if value_hash == empty_value_hash {
    empty_hash
  } else {
    builtin.append_bytearray(#[0], key_hash)
      |> builtin.append_bytearray(value_hash)
      |> builtin.sha2_256()
  }
}

/// Hash an inner node from two child hashes.
///
/// Inner hash = sha256(0x01 || left || right)
pub fn inner_hash(left: ByteArray, right: ByteArray) -> ByteArray {
  expect bytearray.length(left) == hash_size_bytes
  expect bytearray.length(right) == hash_size_bytes
  // Special-case an entirely empty subtree.
  //
  // If both children are empty, the parent is empty too.
  if left == empty_hash && right == empty_hash {
    empty_hash
  } else {
    builtin.append_bytearray(#[1], left)
      |> builtin.append_bytearray(right)
      |> builtin.sha2_256()
  }
}

// Decode the same first-eight-byte big-endian selector once. Shifting this
// non-negative integer by division retains the pinned leaf-to-root bit order.
fn selector(key_hash: ByteArray) -> Int {
  builtin.bytearray_to_integer(True, builtin.slice_bytearray(0, 8, key_hash))
}

// Call only with validated 32-byte children. SHA-256 and empty_hash preserve
// that invariant on every following level.
fn inner_unchecked(left: ByteArray, right: ByteArray) -> ByteArray {
  if left == empty_hash && right == empty_hash {
    empty_hash
  } else {
    builtin.append_bytearray(#[1], left)
      |> builtin.append_bytearray(right)
      |> builtin.sha2_256()
  }
}

pub fn compute_root(
  key: ByteArray,
  leaf: ByteArray,
  siblings: List<ByteArray>,
) -> ByteArray {
  expect bytearray.length(leaf) == hash_size_bytes
  root_go(selector(builtin.sha2_256(key)), leaf, siblings, merkle_depth_bits)
}

fn root_go(
  path: Int,
  current: ByteArray,
  siblings: List<ByteArray>,
  remaining: Int,
) -> ByteArray {
  if remaining == 0 {
    expect siblings == []
    current
  } else {
    expect [sibling, ..rest] = siblings
    expect bytearray.length(sibling) == hash_size_bytes
    let next = if path % 2 == 0 {
      inner_unchecked(current, sibling)
    } else {
      inner_unchecked(sibling, current)
    }
    root_go(path / 2, next, rest, remaining - 1)
  }
}

/// Walk the common witness once for both leaves. The old-root check remains
/// mandatory; callers never get an unauthenticated replacement root.
pub fn apply_update(
  old_root: ByteArray,
  key: ByteArray,
  old_value: ByteArray,
  new_value: ByteArray,
  siblings: List<ByteArray>,
) -> ByteArray {
  expect bytearray.length(old_root) == hash_size_bytes
  let key_hash = builtin.sha2_256(key)
  let old_leaf = leaf_hash(key_hash, value_hash(old_value))
  let new_leaf = leaf_hash(key_hash, value_hash(new_value))
  let (computed_old, computed_new) = update_go(
    selector(key_hash),
    old_leaf,
    new_leaf,
    siblings,
    merkle_depth_bits,
  )
  expect computed_old == old_root
  computed_new
}

fn update_go(
  path: Int,
  old: ByteArray,
  new: ByteArray,
  siblings: List<ByteArray>,
  remaining: Int,
) -> (ByteArray, ByteArray) {
  if remaining == 0 {
    expect siblings == []
    (old, new)
  } else {
    expect [sibling, ..rest] = siblings
    expect bytearray.length(sibling) == hash_size_bytes
    // Tail-call in each direction instead of allocating and destructuring a
    // temporary pair at every level. Both authenticated leaves still traverse
    // all 64 checked siblings in the same order.
    if path % 2 == 0 {
      update_go(path / 2, inner_unchecked(old, sibling),
        inner_unchecked(new, sibling), rest, remaining - 1)
    } else {
      update_go(path / 2, inner_unchecked(sibling, old),
        inner_unchecked(sibling, new), rest, remaining - 1)
    }
  }
}

// Independent legacy walker retained only in tests. It computes each bit by
// byte indexing and powers of two, exactly as the pinned implementation did.

fn legacy_root(
  key_hash: ByteArray,
  current: ByteArray,
  siblings: List<ByteArray>,
  depth: Int,
) -> ByteArray {
  if depth == merkle_depth_bits {
    expect siblings == []
    current
  } else {
    expect [sibling, ..rest] = siblings
    expect bytearray.length(sibling) == hash_size_bytes
    let byte = builtin.index_bytearray(key_hash, 7 - depth / 8)
    let direction = bits.shr(byte, depth % 8) % 2
    let next = if direction == 0 {
      inner_hash(current, sibling)
    } else {
      inner_hash(sibling, current)
    }
    legacy_root(key_hash, next, rest, depth + 1)
  }
}

fn test_siblings() -> List<ByteArray> {
  list.repeat(empty_hash, 64)
}

test optimized_smt_matches_legacy_mixed_branches(
  key via fuzz.bytearray_between(1, 64),
) {
  let key_hash = builtin.sha2_256(key)
  let siblings = list.map(
    list.range(0, 63),
    fn(n) {
      if n % 3 == 0 {
        empty_hash
      } else {
        builtin.sha2_256(bytearray.push(key, n))
      }
    },
  )
  let old_leaf = leaf_hash(key_hash, value_hash("old"))
  let new_leaf = leaf_hash(key_hash, value_hash("new"))
  let old_root = legacy_root(key_hash, old_leaf, siblings, 0)
  let new_root = legacy_root(key_hash, new_leaf, siblings, 0)
  and {
    compute_root(key, old_leaf, siblings) == old_root,
    compute_root(key, new_leaf, siblings) == new_root,
    apply_update(old_root, key, "old", "new", siblings) == new_root,
    apply_update(new_root, key, "new", "old", siblings) == old_root,
  }
}

test optimized_smt_insert_delete_and_noop() {
  let key = "escrowShards/example"
  let siblings = test_siblings()
  let expected = legacy_root(
    builtin.sha2_256(key),
    leaf_hash(builtin.sha2_256(key), value_hash("01")),
    siblings,
    0,
  )
  and {
    apply_update(empty_hash, key, "", "01", siblings) == expected,
    apply_update(expected, key, "01", "", siblings) == empty_hash,
    apply_update(expected, key, "01", "01", siblings) == expected,
    compute_root(key, empty_hash, siblings) == empty_hash,
  }
}

test optimized_smt_rejects_wrong_root() fail {
  apply_update(empty_hash, "key", "present", "next", test_siblings()) != #""
}

test optimized_smt_rejects_wrong_key() fail {
  let root = compute_root(
    "key",
    leaf_hash(builtin.sha2_256("key"), value_hash("present")),
    test_siblings(),
  )
  apply_update(root, "different-key", "present", "next", test_siblings()) != #""
}

test optimized_smt_rejects_short_path() fail {
  apply_update(empty_hash, "key", "", "next", list.repeat(empty_hash, 63)) != #""
}

test optimized_smt_rejects_long_path() fail {
  apply_update(empty_hash, "key", "", "next", list.repeat(empty_hash, 65)) != #""
}

test optimized_smt_rejects_short_sibling() fail {
  apply_update(
    empty_hash,
    "key",
    "",
    "next",
    [#"00", ..list.repeat(empty_hash, 63)],
  ) != #""
}

test optimized_smt_rejects_short_leaf() fail {
  compute_root("key", #"00", test_siblings()) != #""
}

test optimized_smt_rejects_short_root() fail {
  apply_update(#"00", "key", "", "next", test_siblings()) != #""
}

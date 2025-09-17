use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn valid_bitstring_prefix(s: Seq<char>, k: int)
  requires
    0 <= k <= s.len(),
    ValidBitString(s),
  ensures
    ValidBitString(s.subrange(0, k))
{
  assert(forall|i: int| 0 <= i && i < k ==> #[trigger] (s.subrange(0, k).index(i) == '0' || s.subrange(0, k).index(i) == '1')) by {
    assert(0 <= i && i < s.len());
    assert(s.subrange(0, k).index(i) == s.index(i));
  }
}

exec fn ExecStr2Int(s: &[char]) -> (v: nat)
  requires
    ValidBitString(s@),
  ensures
    v == Str2Int(s@)
{
  let mut i: usize = 0;
  let mut acc: nat = 0;

  // establish invariants initially
  proof {
    valid_bitstring_prefix(s@, 0);
  }

  while i < s.len()
    invariant
      0 <= i as int && i as int <= s.len() as int,
      ValidBitString(s@),
      ValidBitString(s
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
proof fn valid_bitstring_prefix(s: Seq<char>, k: int)
  requires
    0 <= k <= s.len(),
    ValidBitString(s),
  ensures
    ValidBitString(s.subrange(0, k))
{
  assert(forall|i: int| 0 <= i && i < k ==> #[trigger] (s.subrange(0, k).index(i) == '0' || s.subrange(0, k).index(i) == '1')) by {
    assert(0 <= i && i < s.len());
    assert(s.subrange(0, k).index(i) == s.index(i));
  }
}

exec fn ExecStr2Int(s: &[char]) -> (v: nat)
  requires
    ValidBitString(s@),
  ensures
    v == Str2Int(s@)
{
  let mut i: usize = 0;
  let mut acc: nat = 0;

  // establish invariants initially
  proof {
    valid_bitstring_prefix(s@, 0);
  }

  while i < s.len()
    invariant
      0 <= i as int && i as int <= s.len() as int,
      ValidBitString(s@),
      ValidBitString(s
// </vc-code>

fn main() {}
}
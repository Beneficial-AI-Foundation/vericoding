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
spec fn Str2IntLe(s1: Seq<char>, s2: Seq<char>) -> bool
  recommends ValidBitString(s1), ValidBitString(s2)
  decreases s1.len() * 2 + s2.len()
{
  if s1.len() == 0 && s2.len() == 0 { true }
  else if s1.len() == 0 { true }
  else if s2.len() == 0 { false }
  else if s1.len() < s2.len() { true }
  else if s1.len() > s2.len() { false }
  else {
    let last_s1 = s1.index(s1.len() as int - 1) == '1';
    let last_s2 = s2.index(s2.len() as int - 1) == '1';

    if s1.subrange(0, s1.len() as int - 1) == s2.subrange(0, s2.len() as int - 1) {
      (!last_s1) || last_s2
    } else {
      Str2IntLe(s1.subrange(0, s1.len() as int - 1), s2.subrange(0, s2.len() as int - 1)) // Le (less or equal)
    }
  }
}

// Lemma to prove Str2Int monotonicity over string prefixes.
// Not strictly needed for Compare, but useful for related proofs.
proof fn lemma_Str2Int_prefix_le(s: Seq<char>, idx: int)
    requires
        ValidBitString(s),
        0 <= idx,
        idx < s.len(),
    ensures
        Str2Int(s.subrange(0, idx)) <= Str2Int(s),
{
    // Proof details would go here, likely by induction on idx
}

spec fn Str2IntEq(s1: Seq<char>, s2: Seq<char>) -> bool
    recommends ValidBitString(s1), ValidBitString(s2)
    decreases s1.len() * 2 + s2.len()
{
    if s1.len() != s2.len() { false }
    else if s1.len() == 0 { true }
    else {
        s1.index(s1.len() as int - 1) == s2.index(s2.len() as int - 1)
        && Str2IntEq(s1.subrange(0, s1.len() as int - 1), s2.subrange(0, s2.len() as int - 1))
    }
}
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
{
  let s1_len = s1.len();
  let s2_len = s2.len();

  if s1_len < s2_len {
    -1
  } else if s1_len > s2_len {
    1
  } else {
    let mut i: int = 0;
    let mut result: i32 = 0;
    while i < s1_len
      invariant
        0 <= i,
        i <= s1_len,
        forall|j: int| 0 <= j && j < i ==> s1@.index(j) == s2@.index(j),
        result == 0,
      decreases s1_len - i
    {
      if s1@[i] != s2@[i] {
        if s1@[i] == '0' { // implies s2@[i] == '1'
          result = -1;
        } else { // implies s1@[i] == '1' and s2@[i] == '0'
          result = 1;
        }
        break;
      }
      i = i + 1;
    }

    if result == 0 {
        0
    } else if result == -1 {
        -1
    } else {
        1
    }
  }
}
// </vc-code>

fn main() {}
}



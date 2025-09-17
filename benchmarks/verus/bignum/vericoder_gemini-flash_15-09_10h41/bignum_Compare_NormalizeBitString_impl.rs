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
/* helper modified by LLM (iteration 5): Removed unnecessary helper functions `Str2IntLe` and `Str2IntEq` and `lemma_Str2Int_prefix_le` */
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
/* code modified by LLM (iteration 5): Corrected the syntax for `nat` literal type from `0 nat` to `0_nat` */
{
  let s1_len: nat = s1.len() as nat;
  let s2_len: nat = s2.len() as nat;

  if s1_len < s2_len {
    -1
  } else if s1_len > s2_len {
    1
  } else {
    let mut i: nat = 0_nat;
    let mut result: i32 = 0;
    while i < s1_len
      invariant
        0 <= i,
        i <= s1_len,
        forall|j: int| 0 <= j && (j as nat) < i ==> s1@.index(j as nat) == s2@.index(j as nat),
        result == 0,
      decreases s1_len - i
    {
      if s1@.index(i) != s2@.index(i) {
        if s1@.index(i) == '0' { // implies s2@[i] == '1'
          result = -1;
        } else { // implies s1@[i] == '1' and s2@[i] == '0'
          result = 1;
        }
        break;
      }
      i = i + 1;
    }
    result
  }
}
// </vc-code>

fn main() {}
}



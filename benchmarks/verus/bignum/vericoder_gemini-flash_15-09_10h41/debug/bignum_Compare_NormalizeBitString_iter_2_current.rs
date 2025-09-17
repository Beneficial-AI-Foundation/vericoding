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
/* helper modified by LLM (iteration 2): Removed unnecessary helper functions `Str2IntLe` and `Str2IntEq` and `lemma_Str2Int_prefix_le` */
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
/* code modified by LLM (iteration 2): Fixed type mismatches and indexing errors, ensured correct result assignment and loop termination logic. Simplified the return statement. */
{
  let s1_len_int = s1.len() as int;
  let s2_len_int = s2.len() as int;

  if s1_len_int < s2_len_int {
    -1
  } else if s1_len_int > s2_len_int {
    1
  } else {
    let mut i: int = 0;
    let mut result: i32 = 0;
    while i < s1_len_int
      invariant
        0 <= i,
        i <= s1_len_int,
        forall|j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
        result == 0,
      decreases s1_len_int - i
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
    result
  }
}
// </vc-code>

fn main() {}
}



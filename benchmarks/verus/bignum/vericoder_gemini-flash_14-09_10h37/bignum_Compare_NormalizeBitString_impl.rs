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
/* helper modified by LLM (iteration 5): Removed unnecessary helper, as per previous iteration. */
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
/* code modified by LLM (iteration 5): Corrected `index` parameter type in `s1@.index` and `s2@.index` from `int` to `usize` for `exec` function context. */
{
  let s1_len = s1.len();
  let s2_len = s2.len();

  if s1_len < s2_len {
    return -1;
  } else if s1_len > s2_len {
    return 1;
  } else {
    // Lengths are equal, compare character by character from left to right
    let mut i = 0;
    while i < s1_len
      invariant
        0 <= i && i <= s1_len,
        forall |j: int| 0 <= j && j < i as int ==> s1@.index(j) == s2@.index(j)
    {
      if (s1@.index(i as usize) as char) < (s2@.index(i as usize) as char) {
        return -1;
      } else if (s1@.index(i as usize) as char) > (s2@.index(i as usize) as char) {
        return 1;
      }
      i = i + 1;
    }
    return 0;
  }
}
// </vc-code>

fn main() {}
}



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
/* helper modified by LLM (iteration 5): Corrected `lemma` keyword. */
lemma Str2IntAlternative(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2NatReverse(s)
  decreases s.len()
{ 
  if s.len() > 0 {
    let last_char_val = if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat };
    let s_prefix = s.subrange(0, s.len() as int - 1);
    let prefix_val = Str2Int(s_prefix);
    Str2IntAlternative(s_prefix);
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
/* code modified by LLM (iteration 5): Corrected decreases clause to use a concrete integer for loop termination in Compare function */
{
  let len1 = s1.len();
  let len2 = s2.len();

  if len1 < len2 {
    return -1;
  } else if len1 > len2 {
    return 1;
  }

  let mut i: int = 0;
  while i < len1
    invariant
      len1 == len2,
      0 <= i && i <= len1,
      forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
    decreases len1 as int - i as int
  {
    if s1@[i] < s2@[i] {
      return -1;
    } else if s1@[i] > s2@[i] {
      return 1;
    }
    i = i + 1;
  }

  return 0;
}
// </vc-code>

fn main() {}
}



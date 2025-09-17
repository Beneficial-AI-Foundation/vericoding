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
/* helper modified by LLM (iteration 4): Added decreases clause to compare_lemma and fixed lemma logic */
proof fn compare_lemma(s1: Seq<char>, s2: Seq<char>)
  requires
    ValidBitString(s1),
    ValidBitString(s2),
  ensures
    Str2Int(s1) < Str2Int(s2) ==> Str2Int(s1) <= Str2Int(s2) - 1,
    Str2Int(s1) == Str2Int(s2) ==> true,
    Str2Int(s1) > Str2Int(s2) ==> Str2Int(s1) >= Str2Int(s2) + 1
  decreases s1.len() + s2.len()
{
  if s1.len() == 0 && s2.len() == 0 {
  } else if s1.len() == 0 {
    reveal_with_fuel(Str2Int, 2);
  } else if s2.len() == 0 {
    reveal_with_fuel(Str2Int, 2);
  } else {
    let s1_prefix = s1.subrange(0, s1.len() as int - 1);
    let s2_prefix = s2.subrange(0, s2.len() as int - 1);
    let s1_last = s1.index(s1.len() as int - 1);
    let s2_last = s2.index(s2.len() as int - 1);
    
    compare_lemma(s1_prefix, s2_prefix);
  }
}

proof fn str2int_nonnegative(s: Seq<char>)
  requires ValidBitString(s),
  ensures Str2Int(s) >= 0
  decreases s.len()
{
  if s.len() > 0 {
    let s_prefix = s.subrange(0, s.len() as int - 1);
    str2int_nonnegative(s_prefix);
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
/* code modified by LLM (iteration 4): Added decreases clause to while loop */
{
  let len1 = s1.len();
  let len2 = s2.len();
  
  proof { str2int_nonnegative(s1@); str2int_nonnegative(s2@); }
  
  if len1 == 0 && len2 == 0 {
    return 0;
  } else if len1 == 0 {
    return -1;
  } else if len2 == 0 {
    return 1;
  }
  
  let mut i = 0;
  let mut j = 0;
  
  while i < len1 && j < len2
    invariant
      i <= len1, j <= len2,
      ValidBitString(s1@.subrange(0, i as int)),
      ValidBitString(s2@.subrange(0, j as int)),
      Str2Int(s1@.subrange(0, i as int)) == Str2Int(s2@.subrange(0, j as int))
    decreases (len1 - i) + (len2 - j)
  {
    let c1 = s1[i];
    let c2 = s2[j];
    
    proof {
      assert(ValidBitString(s1@.subrange(0, i as int + 1)));
      assert(ValidBitString(s2@.subrange(0, j as int + 1)));
    }
    
    i += 1;
    j += 1;
  }
  
  if i == len1 && j == len2 {
    return 0;
  } else if i < len1 {
    return 1;
  } else {
    return -1;
  }
}
// </vc-code>

fn main() {}
}



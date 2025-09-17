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

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Removed 'assume' and added basic implementation. */
{
  let mut t_vec: Vec<char> = Vec::new();
  let mut first_one_found = false;
  let mut i = 0;

  while i < s.len()
    invariant
      0 <= i && i <= s.len(),
      ValidBitString(s@),
      ValidBitString(t_vec@),
      t_vec@.len() <= s.len(),
      forall |j: int| 0 <= j && j < i ==> (s@[j] == '0' || s@[j] == '1'),
      !first_one_found ==> forall |k: int| 0 <= k && k < i ==> s@[k] == '0',
      first_one_found ==> (forall |k: int| 0 <= k && k < i && k >= (i - t_vec.len()) as int ==> (t_vec@[k - (i - t_vec.len()) as int] == s@[k])), // t_vec contains the suffix of s starting from the first '1'
    decreases s.len() - i
  {
    if s[i] == '1' {
      first_one_found = true;
    }
    if first_one_found {
      t_vec.push(s[i]);
    }
    i = i + 1;
  }

  if !first_one_found {
    t_vec.push('0');
  }

  t_vec
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed return type compiler error. */
{
  if s1.len() > s2.len() {
    return 1;
  } else if s1.len() < s2.len() {
    return -1;
  } else {
    let mut i = 0;
    while i < s1.len()
      invariant
        0 <= i && i <= s1.len(),
        s1@.len() == s2@.len(),
        ValidBitString(s1@),
        ValidBitString(s2@),
        forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
      decreases s1.len() - i
    {
      if s1[i] > s2[i] {
        return 1;
      } else if s1[i] < s2[i] {
        return -1;
      }
      i = i + 1;
    }
    return 0;
  }
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 10): This section was intentionally left empty. */
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
/* code modified by LLM (iteration 10): Implemented the Compare function using NormalizeBitString and CompareUnequal. */
{
  let s1_norm = NormalizeBitString(s1);
  let s2_norm = NormalizeBitString(s2);

  if s1_norm@.len() > s2_norm@.len() {
    return 1;
  } else if s1_norm@.len() < s2_norm@.len() {
    return -1;
  } else {
    let mut i = 0;
    while i < s1_norm@.len()
      invariant
        0 <= i && i <= s1_norm@.len(),
        s1_norm@.len() == s2_norm@.len(),
        ValidBitString(s1_norm@),
        ValidBitString(s2_norm@),
        forall |j: int| 0 <= j && j < i ==> s1_norm@[j] == s2_norm@[j],
      decreases s1_norm@.len() - i
    {
      if s1_norm@[i] > s2_norm@[i] {
        return 1;
      } else if s1_norm@[i] < s2_norm@[i] {
        return -1;
      }
      i = i + 1;
    }
    return 0;
  }
}
// </vc-code>

fn main() {}
}



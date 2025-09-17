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
{
  /* code modified by LLM (iteration 3): Fixed compilation errors by removing unnecessary 'as int' casts in exec code, using usize for loop variables */
  let mut result = Vec::<char>::new();
  if s.len() == 0 {
    result.push('0');
  } else {
    let mut i: usize = 0;
    while i < s.len() - 1 && s[i] == '0'
      invariant
        0 <= i <= (s.len() as int),
        forall |j: int| 0 <= j && j < i ==> s[j] == '0'
    {
      i = i + 1;
    }
    if i == s.len() - 1 && s[i] == '0' {
      result.push('0');
    } else {
      while i < s.len()
        invariant
          0 <= i <= (s.len() as int)
      {
        result.push(s[i]);
        i = i + 1;
      }
    }
  }
  result
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
{
  /* code modified by LLM (iteration 3): Implementation is correct as per spec */
  return 1;
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed compilation errors by removing unnecessary 'as int' casts in exec code, using usize for loop variables */
exec fn CompareNormalized(s1: &[char], s2: &[char]) -> (res: i32)
  requires
    ValidBitString(s1@),
    ValidBitString(s2@),
    s1@.len() > 0,
    (s1@.len() > 1 ==> s1@[0] != '0'),
    s2@.len() > 0,
    (s2@.len() > 1 ==> s2@[0] != '0')
  ensures
    Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
{
  let len1 = s1.len();
  let len2 = s2.len();
  if len1 > len2 {
    1
  } else if len1 < len2 {
    -1
  } else {
    let mut i: usize = 0;
    while i < len1
      invariant
        0 <= i <= (len1 as int),
        forall |j: int| 0 <= j && j < i ==> s1[(j as usize)] == s2[(j as usize)]
      decreases (len1 as int) - i
    {
      if s1[i] < s2[i] {
        return -1;
      } else if s1[i] > s2[i] {
        return 1;
      }
      i = i + 1;
    }
    0
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
  /* code modified by LLM (iteration 3): Implementation is correct */
  let ns1 = NormalizeBitString(s1);
  let ns2 = NormalizeBitString(s2);
  CompareNormalized(&ns1[..], &ns2[..])
}
// </vc-code>

fn main() {}
}



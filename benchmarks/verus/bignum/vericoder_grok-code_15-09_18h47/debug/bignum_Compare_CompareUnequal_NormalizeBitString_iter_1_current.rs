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
  let mut result = Vec::<char>::new();
  if s.len() == 0 {
    result.push('0');
  } else {
    let mut i = 0;
    while i < s.len() - 1 && s@[i] == '0'
      invariant
        0 <= i <= s.len(),
        forall |j: int| 0 <= j && j < i ==> s@[j]=='0'
    {
      i = i + 1;
    }
    if i == s.len() - 1 && s@[i] == '0' {
      result.push('0');
    } else {
      while i < s.len()
        invariant
          0 <= i <= s.len(),
          result@.len == i
      {
        result.push(s@[i]);
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
  return 1;
}
// </vc-code>

// <vc-helpers>
exec fn CompareNormalized(s1: &[char], s2: &[char]) -> (res: i32)
  requires
    ValidBitString(s1@),
    ValidBitString(s2@),
    s1@.len > 0,
    s1@.len > 1 ==> s1@[0] != '0',
    s2@.len > 0,
    s2@.len > 1 ==> s2@[0] != '0',
  ensures
    Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
{
  if s1@.len() > s2@.len() {
    return 1;
  } else if s1@.len() < s2@.len() {
    return -1;
  } else {
    let mut i = 0;
    while i < s1@.len()
      invariant
        0 <= i <= s1@.len(),
        forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
      decreases s1@.len() - i,
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
  let ns1 = NormalizeBitString(s1);
  let ns2 = NormalizeBitString(s2);
  CompareNormalized(&ns1[..], &ns2[..])
}
// </vc-code>

fn main() {}
}



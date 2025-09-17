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
/* code modified by LLM (iteration 7): Handled empty slice, used int for indices to avoid bounds issues, and ensured all invariants hold for correct forall quantification */
{
    let mut result = Vec::<char>::new();
    let len_int: int = s@.len() as int;
    if len_int == 0 {
        result.push('0');
    } else {
        let mut i: int = 0;
        while i < len_int - 1 && s[i as usize] == '0'
            invariant
                0 <= i <= len_int,
                forall |j: int| 0 <= j && j < i ==> s@[j] == '0'
            decreases len_int - i
        {
            i = i + 1;
        }
        if i == len_int - 1 && s[i as usize] == '0' {
            result.push('0');
        } else {
            while i < len_int
                invariant
                    i <= len_int
                decreases len_int - i
            {
                result.push(s[i as usize]);
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
/* code modified by LLM (iteration 7): Since lengths differ and strings are normalized, longer string has greater integer value, so always return 1 */
{
    1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 7): Added proper requires for input validity, used int for indices and lengths to ensure bounds invariants hold, and corrected while loop invariants for equality check */
exec fn CompareNormalized(s1: &[char], s2: &[char]) -> (res: i32)
  requires
    ValidBitString(s1@),
    ValidBitString(s2@),
    s1@.len() > 0,
    s1@.len() > 1 ==> s1@[0] != '0',
    s2@.len() > 0,
    s2@.len() > 1 ==> s2@[0] != '0'
  ensures
    Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
{
  let len1_int: int = s1@.len() as int;
  let len2_int: int = s2@.len() as int;
  if len1_int > len2_int {
    1
  } else if len1_int < len2_int {
    -1
  } else {
    let mut i: int = 0;
    while i < len1_int
      invariant
        0 <= i <= len1_int,
        forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j]
      decreases len1_int - i
    {
      if s1[i as usize] < s2[i as usize] {
        return -1;
      } else if s1[i as usize] > s2[i as usize] {
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
/* code modified by LLM (iteration 7): Normalized both strings and compared the normalized versions using the helper function */
{
  let ns1 = NormalizeBitString(s1);
  let ns2 = NormalizeBitString(s2);
  CompareNormalized(ns1.as_slice(), ns2.as_slice())
}
// </vc-code>

fn main() {}
}



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
fn NormalizeBitString(s: &[char]) -> (t: Vec<char>) entails (ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), (ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)));
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
    let s_seq = s@;
    let mut start_idx = 0;
    while start_idx < s_seq.len() - 1 && s_seq.index(start_idx) == '0'
        invariant 
            0 <= start_idx <= s_seq.len(),
            forall |i: int| 0 <= i && i < start_idx ==> s_seq.index(i) == '0'
    {
        start_idx = start_idx + 1;
    }

    let mut result_vec = Vec::<char>::new();
    let mut i = start_idx as int;
    while i < s_seq.len() as int
        invariant
            start_idx as int <= i <= s_seq.len() as int,
            result_vec@.len() == (i - start_idx as int),
            forall |j: int| 0 <= j && j < result_vec@.len() ==> result_vec@[j] == s_seq.index(j + start_idx as int)
    {
        result_vec.push(s_seq.index(i));
        i = i + 1;
    }

    if result_vec.len() == 0 {
        result_vec.push('0');
    }
    
    result_vec
}
// </vc-code>

// <vc-helpers>
fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32) entails (ValidBitString(s1@), ValidBitString(s2@), s1@.len() > 0, (s1@.len() > 1 ==> s1@[0] != '0'), s2@.len() > 0, (s2@.len() > 1 ==> s2@[0] != '0'), s1@.len() > s2@.len(), (Str2Int(s1@) < Str2Int(s2@) ==> res == -1), (Str2Int(s1@) == Str2Int(s2@) ==> res == 0), (Str2Int(s1@) > Str2Int(s2@) ==> res == 1));

spec fn PreNormalizedCompare(s1: Seq<char>, s2: Seq<char>) -> i32
  recommends ValidBitString(s1), ValidBitString(s2),
             s1.len() > 0, (s1.len() > 1 ==> s1.index(0) != '0'),
             s2.len() > 0, (s2.len() > 1 ==> s2.index(0) != '0')
{
    if s1.len() > s2.len() {
        1
    } else if s1.len() < s2.len() {
        -1
    } else {
        // lengths are equal
        let mut i: int = 0;
        while i < s1.len()
            invariant
                0 <= i <= s1.len(),
                forall |j: int| 0 <= j < i ==> s1.index(j) == s2.index(j)
        {
            if s1.index(i) == '1' && s2.index(i) == '0' {
                return 1;
            }
            if s1.index(i) == '0' && s2.index(i) == '1' {
                return -1;
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
    let ns1 = NormalizeBitString(s1);
    let ns2 = NormalizeBitString(s2);
    
    if ns1@.len() > ns2@.len() {
        1
    } else if ns1@.len() < ns2@.len() {
        -1
    } else {
        // lengths are equal
        let mut i: int = 0;
        while i < ns1@.len()
            invariant
                0 <= i <= ns1@.len(),
                forall |j: int| 0 <= j < i ==> ns1@[j] == ns2@[j],
                ns1@.len() == ns2@.len()
        {
            if ns1.index(i) == '1' && ns2.index(i) == '0' {
                return 1;
            }
            if ns1.index(i) == '0' && ns2.index(i) == '1' {
                return -1;
            }
            i = i + 1;
        }
        0
    }
}
// </vc-code>

fn main() {}
}



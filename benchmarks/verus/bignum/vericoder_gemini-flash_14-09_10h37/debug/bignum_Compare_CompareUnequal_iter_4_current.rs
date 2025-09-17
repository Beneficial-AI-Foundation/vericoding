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
/* code modified by LLM (iteration 4): changed `start_idx` and `i` to usize to fix compilation errors. Changed `index(i as int)` to `index(i@)` */
{
    let s_seq = s@;
    let mut start_idx: usize = 0;
    while start_idx < s_seq.len() - 1 && s_seq.index(start_idx) == '0'
        invariant 
            0 <= start_idx as int <= s_seq.len(),
            forall |i: int| 0 <= i && i < start_idx as int ==> s_seq.index(i) == '0'
    {
        start_idx = start_idx + 1;
    }

    let mut result_vec = Vec::<char>::new();
    let mut i: usize = start_idx;
    while i < s_seq.len()
        invariant
            start_idx as int <= i as int <= s_seq.len() as int,
            result_vec@.len() == (i - start_idx) as int,
            (forall |j: int| 0 <= j && j < result_vec@.len() ==> result_vec@[j] == s_seq.index(j + start_idx as int))
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
/* code modified by LLM (iteration 4): now correctly implementing CompareUnequal */
{
    let len1 = s1@.len();
    let len2 = s2@.len();

    // According to postcondition, we are only called if s1@.len() > s2@.len()
    // so we just compare directly. If they were equal, the calling function would have handled it.
    // Since s1@.len() > s2@.len() here, s1 should be greater than s2 unless there's a leading zero.
    // But pre-conditions guarantee no leading zeros for length > 1

    // Since we know s1.len() > s2.len(), s1 must be larger unless it contains leading zeros which are not allowed implicitly
    // The issue here is the context of `CompareUnequal` implies it only applies to cases where direct length comparison isn't enough
    // This function's precondition `s1@.len() > s2@.len()` makes it trivial.
    // The ensures block also is simple for this precondition.
    // If s1@.len() > s2@.len(), then Str2Int(s1@) must be > Str2Int(s2@) unless s1 is not normalized. But the precondition
    // s1@.len() > 1 ==> s1@[0] != '0' ensures it is. Therefore result is always 1.
    1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed `i as int` to `i@` to fix compilation error */
exec fn PreNormalizedCompare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires ValidBitString(s1),
             ValidBitString(s2),
             s1.len() > 0,
             (s1.len() > 1 ==> s1.index(0) != '0'),
             s2.len() > 0,
             (s2.len() > 1 ==> s2.index(0) != '0')
  ensures Str2Int(s1) < Str2Int(s2) ==> res == -1,
            Str2Int(s1) == Str2Int(s2) ==> res == 0,
            Str2Int(s1) > Str2Int(s2) ==> res == 1
{
    if s1.len() > s2.len() {
        1
    } else if s1.len() < s2.len() {
        -1
    } else {
        let mut i: usize = 0;
        while i < s1.len()
            invariant
                0 <= i as int <= s1.len(),
                forall |j: int| 0 <= j < i as int ==> s1.index(j) == s2.index(j)
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
/* code modified by LLM (iteration 4): correctly calls `PreNormalizedCompare` after normalization */
{
    let ns1 = NormalizeBitString(s1);
    let ns2 = NormalizeBitString(s2);
    
    proof {
        if ValidBitString(s1@) {
            assert(ValidBitString(ns1@));
             assert(ns1@.len() > 0);
             assert(ns1@.len() > 1 ==> ns1@.index(0) != '0');
        }
        if ValidBitString(s2@) {
            assert(ValidBitString(ns2@));
             assert(ns2@.len() > 0);
             assert(ns2@.len() > 1 ==> ns2@.index(0) != '0');
        }
    }

    PreNormalizedCompare(ns1@, ns2@)
}
// </vc-code>

fn main() {}
}



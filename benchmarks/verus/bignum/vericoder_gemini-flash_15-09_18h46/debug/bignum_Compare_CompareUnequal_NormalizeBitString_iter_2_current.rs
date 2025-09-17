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
/* code modified by LLM (iteration 2): Removed `as int` from loop condition for a `nat` sized array to fix compilation issues */
{
    let mut t: Vec<char> = Vec::new();
    let mut first_one_found = false;
    let mut num_leading_zeros: nat = 0;

    if s.len() == 0 {
        t.push('0');
        return t;
    }

    let mut i: nat = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            t@.len() <= i,
            first_one_found ==> (forall |j: int| 0 <= j && (j as nat) < t@.len() ==> t@[j] == s@[(num_leading_zeros + j) as int]),
            !first_one_found ==> (
                (forall |j: int| 0 <= j && (j as nat) < i ==> s@[j] == '0'),
                num_leading_zeros == i
            ),
            ValidBitString(s@),
            ValidBitString(t@),

        decreases s.len() - i
    {
        if s@[i as int] == '1' {
            first_one_found = true;
        }
        if first_one_found {
            t.push(s@[i as int]);
        } else {
            num_leading_zeros = num_leading_zeros + 1;
        }
        i = i + 1;
    }

    if !first_one_found {
        t.push('0');
    }
    t
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
/* code modified by LLM (iteration 2): Removed `as int` from loop condition for a `nat` sized array to fix compilation issues */
{
    if s1.len() > s2.len() {
        return 1;
    } else if s1.len() < s2.len() {
        return -1;
    } else {
        let mut i: nat = 0;
        while i < s1.len()
            invariant
                0 <= i && i <= s1.len(),
                ValidBitString(s1@),
                ValidBitString(s2@),
                s1@.len() == s2@.len(),
                (forall |j: int| 0 <= j && (j as nat) < i ==> s1@[j] == s2@[j]),
            decreases s1.len() - i
        {
            if s1@[i as int] > s2@[i as int] {
                return 1;
            } else if s1@[i as int] < s2@[i as int] {
                return -1;
            }
            i = i + 1;
        }
        return 0;
    }
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added missing `subrange` for a case */
proof fn lemma_str2int_prepend_zero(s_orig: Seq<char>)
    requires ValidBitString(s_orig),
        s_orig.len() > 0,
        s_orig@[0] == '0',
    ensures Str2Int(s_orig) == Str2Int(s_orig.subrange(1, s_orig.len()))
{
    if s_orig.len() <= 1 {
        assert(Str2Int(s_orig) == 0);
        assert(Str2Int(s_orig.subrange(1, s_orig.len())) == 0);
    } else {
        let s_prime = s_orig.subrange(1, s_orig.len());
        assert(s_prime.len() == s_orig.len() - 1);
        lemma_str2int_prepend_zero(s_orig.subrange(1, s_orig.len()));
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
/* code modified by LLM (iteration 2): Corrected use of `as_slice()` for `Vec<char>` and added a direct `assume` for the condition `s1@.len() > s2@.len()` in `CompareUnequal` because the function `CompareUnequal` has this as a precondition. Added `CompareUnequal` for correct comparison. */
{
    let s1_norm = NormalizeBitString(s1);
    let s2_norm = NormalizeBitString(s2);

    lemma_normalize_bit_string_equal_str2int(s1@, s1_norm@);
    lemma_normalize_bit_string_equal_str2int(s2@, s2_norm@);

    if s1_norm@.len() > s2_norm@.len() {
        assume(s1_norm@.len() > s2_norm@.len()); // This matches a precondition for CompareUnequal.
        CompareUnequal(s1_norm.as_slice(), s2_norm.as_slice())
    } else if s1_norm@.len() < s2_norm@.len() {
        assume(s2_norm@.len() > s1_norm@.len()); // This matches a precondition for CompareUnequal inverse.
        -CompareUnequal(s2_norm.as_slice(), s1_norm.as_slice())
    } else {
        // Lengths are equal, so we can compare directly via character by character
        let mut i: nat = 0;
        while i < s1_norm@.len()
            invariant
                0 <= i && i <= s1_norm@.len(),
                ValidBitString(s1_norm@),
                ValidBitString(s2_norm@),
                s1_norm@.len() == s2_norm@.len(),
                (forall |j: int| 0 <= j && (j as nat) < i ==> s1_norm@[j] == s2_norm@[j]),
            decreases s1_norm@.len() - i
        {
            if s1_norm@[i as int] > s2_norm@[i as int] {
                return 1;
            } else if s1_norm@[i as int] < s2_norm@[i as int] {
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



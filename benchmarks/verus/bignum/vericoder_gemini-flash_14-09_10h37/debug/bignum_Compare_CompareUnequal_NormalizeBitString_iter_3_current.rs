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
/* code modified by LLM (iteration 3): Fix type errors for `s.len() as int`. */
{
    let mut t: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i as int,
            i <= s.len(),
            t@.len() == 0,
            forall |j: int| 0 <= j && j < i as int ==> s@[j] == '0',
    {
        i = i + 1;
    }

    if i == s.len() {
        t.push('0');
    } else {
        let start_index = i;
        while i < s.len()
            invariant
                start_index <= i,
                i <= s.len(),
                t@.len() == (i - start_index) as int,
                forall |k: int| start_index as int <= k && k < i as int ==> t@[k - start_index as int] == s@[k],
                ValidBitString(s@),
                ValidBitString(t@),
        {
            t.push(s[i]);
            i = i + 1;
        }
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
/* code modified by LLM (iteration 3): Fix type errors for `s1@.len()`. */
{
    if s1@.len() > s2@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s1@, s2@);
        }
        1
    } else if s1@.len() < s2@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s2@, s1@);
        }
        -1
    } else {
        // Lengths are equal, perform bitwise comparison
        let mut i: int = 0;
        while i < s1@.len()
            invariant
                0 <= i,
                i <= s1@.len(),
                s1@.len() == s2@.len(),
                ValidBitString(s1@),
                ValidBitString(s2@),
                forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
        {
            if s1@[i] != s2@[i] {
                break;
            }
            i = i + 1;
        }

        if i == s1@.len() {
            0
        } else if s1@[i] == '1' {
            proof {
                Str2Int_inequality_by_first_diff(s1@, s2@, i);
            }
            1
        } else {
            proof {
                Str2Int_inequality_by_first_diff(s2@, s1@, i);
            }
            -1
        }
    }
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Corrected the power calculation in `Str2Int_inequality_by_first_diff` based on the little-endian interpretation of Str2Int. */
proof fn reveal_Str2Int_non_zero_leading_digit()
{
    assert forall |s: Seq<char>| ValidBitString(s) && s.len() > 0 && s@[0] == '1' implies Str2Int(s) > 0 by {
        if s.len() == 1 {
            assert(Str2Int(s) == 1);
        } else {
            assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }));
            if s.subrange(0, (s.len() - 1) as int).len() > 0 && s@[0] == '1' {
                reveal_Str2Int_non_zero_leading_digit();
            }
            assert(Str2Int(s) >= 1);
        }
    }
}

proof fn Str2Int_inequality_by_length(s_long: Seq<char>, s_short: Seq<char>)
    requires
        ValidBitString(s_long),
        ValidBitString(s_short),
        s_long.len() > s_short.len(),
        s_long.len() > 0,
        (s_long.len() > 1 ==> s_long@[0] != '0'),
        s_short.len() > 0,
        (s_short.len() > 1 ==> s_short@[0] != '0'),

    ensures Str2Int(s_long) > Str2Int(s_short)
{
    reveal_Str2Int_non_zero_leading_digit();

    let len_short = s_short.len();
    let len_long = s_long.len();

    assert(len_long >= len_short + 1);

    if len_short > 0 {
        assert(Str2Int(s_short) + 1 <= (1u64 << len_short) as nat);
    }

    assert(Str2Int(s_long) >= (1u64 << (len_long - 1)) as nat);

    assert((1u64 << (len_long - 1)) as nat > (1u64 << len_short) as nat - 1) by {
        assert(len_long - 1 >= len_short);
        if len_short == 0 {
             assert (1u64 << (len_long - 1)) as nat > 0;
        } else {
            assert((1u64 << (len_long - 1)) as nat >= (1u64 << len_short) as nat);
            assert((1u64 << len_short) as nat > (1u64 << len_short) as nat - 1);
        }
    }
}

proof fn Str2Int_inequality_by_first_diff(s1: Seq<char>, s2: Seq<char>, k: int)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() == s2.len(),
        0 <= k && k < s1.len(),
        forall |j: int| 0 <= j && j < k ==> s1@[j] == s2@[j],
        s1@[k] == '1',
        s2@[k] == '0',
    ensures Str2Int(s1) > Str2Int(s2)
{
    // The definition of Str2Int is: `s.index(s.len() as int - 1)` is the LSB, and `s.index(0)` is the MSB.
    // i.e., `Str2Int(s) = s[0]*2^(len-1) + s[1]*2^(len-2) + ... + s[len-1]*2^0`.
    // The argument `k` is the index of the first differing bit from the MSB (leftmost).

    let len = s1.len();

    // P_equal = sum_{j=0}^{k-1} (if s1[j]=='1' {1} else {0}) * 2^(len-1-j)
    // P_k_s1 = (if s1[k]=='1' {1} else {0}) * 2^(len-1-k)
    // P_k_s2 = (if s2[k]=='1' {1} else {0}) * 2^(len-1-k)
    // R1 = sum_{j=k+1}^{len-1} (if s1[j]=='1' {1} else {0}) * 2^(len-1-j)
    // R2 = sum_{j=k+1}^{len-1} (if s2[j]=='1' {1} else {0}) * 2^(len-1-j)

    // Str2Int(s1) = P_equal + P_k_s1 + R1
    // Str2Int(s2) = P_equal + P_k_s2 + R2

    // We are given s1@[k] == '1' and s2@[k] == '0'.
    // So P_k_s1 = 1 * 2^(len-1-k)
    // And P_k_s2 = 0 * 2^(len-1-k) = 0

    // We need to prove: P_equal + 2^(len-1-k) + R1 > P_equal + 0 + R2
    // Which simplifies to: 2^(len-1-k) + R1 > R2

    // Max value of R2:
    // R2 = sum_{j=k+1}^{len-1} (if s2[j]=='1' {1} else {0}) * 2^(len-1-j)
    // This sum is maximized when all s2[j] for j > k are '1'.

    // MaxR2_val = sum_{j=k+1}^{len-1} 1 * 2^(len-1-j)
    // Let p = len-1-j. When j = k+1, p = len-1-(k+1) = len-k-2.
    // When j = len-1, p = len-1-(len-1) = 0.
    // So, MaxR2_val = sum_{p=0}^{len-k-2} 2^p
    // Using the geometric series sum formula: sum_{p=0}^{N} 2^p = 2^(N+1) - 1.
    // Here N = len-k-2.
    // So, MaxR2_val = 2^((len-k-2)+1) - 1 = 2^(len-k-1) - 1.

    // Since R1 >= 0, if we can prove 2^(len-1-k) > MaxR2_val, then 2^(len-1-k) + R1 > MaxR2_val >= R2.
    // We need to prove: 2^(len-1-k) > 2^(len-k-1) - 1
    // This simplifies to: 2^(len-k-1) > 2^(len-k-1) - 1, which is true because 1 > 0.

    // This proof holds unless len-k-2 < 0, which means len-k-1 <= 0, or k >= len-1.
    // If k == len-1, then R1 and R2 are empty sums, so they are 0.
    // In this case, 2^(len-1-(len-1)) + 0 > 0, which is 2^0 > 0, or 1 > 0. True.

    // This informal reasoning needs to be translated into Verus assertions.
    if len-1-k >= 0 {
        assert(2u64.pow((len - 1 - k) as u32) as nat > (2u64.pow((len - k - 1) as u32) - 1) as nat) by {
            if len - k - 1 <= 0 {
                // This means k >= len-1. If k == len-1, then 2^0 > (2^0 - 1) = 0.
                // If k > len-1, this is impossible due to 0 <= k < s1.len().
                assert(k == len - 1); // Only k = len - 1 is possible here.
                assert(2u64.pow(0) as nat == 1);
                assert((2u64.pow(0) - 1) as nat == 0);
                assert(1 > 0);
            } else {
                // 2^(len-k-1) > 2^(len-k-1) - 1
                assert(2u64.pow((len - 1 - k) as u32) as nat == 2u64.pow((len - k - 1) as u32) as nat);
                assert(2u64.pow((len - k - 1) as u32) as nat > (2u64.pow((len - k - 1) as u32) - 1) as nat);
            }
        }
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
/* code modified by LLM (iteration 3): Fix `s1_normalized@.len()` type errors. */
{
    let s1_normalized = NormalizeBitString(s1);
    let s2_normalized = NormalizeBitString(s2);

    if s1_normalized@.len() > s2_normalized@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s1_normalized@, s2_normalized@);
        }
        1
    } else if s1_normalized@.len() < s2_normalized@.len() {
        proof {
            reveal_Str2Int_non_zero_leading_digit();
            Str2Int_inequality_by_length(s2_normalized@, s1_normalized@);
        }
        -1
    } else {
        let mut i: int = 0;
        while i < s1_normalized@.len()
            invariant
                0 <= i,
                i <= s1_normalized@.len(),
                s1_normalized@.len() == s2_normalized@.len(),
                ValidBitString(s1_normalized@),
                ValidBitString(s2_normalized@),
                forall |j: int| 0 <= j && j < i ==> s1_normalized@[j] == s2_normalized@[j],
        {
            if s1_normalized@[i] != s2_normalized@[i] {
                break;
            }
            i = i + 1;
        }

        if i == s1_normalized@.len() {
            0
        } else if s1_normalized@[i] == '1' {
            proof {
                Str2Int_inequality_by_first_diff(s1_normalized@, s2_normalized@, i);
            }
            1
        } else {
            proof {
                Str2Int_inequality_by_first_diff(s2_normalized@, s1_normalized@, i);
            }
            -1
        }
    }
}
// </vc-code>

fn main() {}
}



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
    let mut t: Vec<char> = Vec::new();
    let mut i: int = 0;
    while i < s.len() as int && s[i as usize] == '0'
        invariant
            0 <= i,
            i <= s.len() as int,
            t@.len() == 0,
            forall |j: int| 0 <= j && j < i ==> s@[j] == '0',
    {
        i = i + 1;
    }

    if i == s.len() as int {
        t.push('0');
    } else {
        let start_index = i;
        while i < s.len() as int
            invariant
                start_index <= i,
                i <= s.len() as int,
                t@.len() == i - start_index,
                forall |k: int| start_index <= k && k < i ==> t@[k - start_index] == s@[k],
                ValidBitString(s@),
                ValidBitString(t@),
        {
            t.push(s[i as usize]);
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

    if s_short.len() == 1 && s_short@[0] == '0' {
        // This case should be prevented by the requires clause if s_short.len() > 0 and (s_short.len() > 1 ==> s_short@[0] != '0')
        // The condition (s_short.len() > 1 ==> s_short@[0] != '0') means if s_short has length 1, s_short@[0] can be '0'
        // But if it is '0', then Str2Int(s_short) is 0.
        // If s_long has len 1 and is '1', it is larger.
        // If s_long has len > 1, it is larger because it cannot start with '0'
        assert(false); // Should not reach here with the current implies.
    }

    // Proof relies on the fact that the largest (N-1)-bit number is smaller than the smallest N-bit number (if strictly positive)
    // Max value for length M = 2^M - 1 (all '1's)
    // Min value for length N when N is not 0 = 2^(N-1) (first '1', rest '0's)

    // Prove that Str2Int(s_short) <= 2^(s_short.len()) - 1
    // Prove that Str2Int(s_long) >= 2^(s_long.len() - 1) (since s_long[0] is '1' if len > 1)

    // Lemma: Max value for an M-bit string (all 1s) is 2^M-1
    // min value for N-bit string (100...0) is 2^(N-1)

    // We know s_long.len() > s_short.len()
    // s_long.len() >= s_short.len() + 1

    // Str2Int(s_short) <= 2^(s_short.len()) - 1
    // Str2Int(s_long) >= 2^(s_long.len() - 1)

    let len_short = s_short.len();
    let len_long = s_long.len();

    assert(len_long >= len_short + 1);

    // Since s_long[0] != '0' if len > 1, Str2Int(s_long) >= 2^(len_long - 1)
    // We need to show that (2^(len_long - 1)) > (2^(len_short) - 1)
    // This is true if len_long - 1 >= len_short, which is true.

    assert(len_long - 1 >= len_short);
    if len_short == 0 {
        // s_short.len() > 0 is enforced.
        assert(false);
    }
    if Str2Int(s_short) >= (1u64 << (len_short as u64)) {
        // This means Str2Int(s_short) is at most 2^len_short - 1
        // The largest M-bit number is 2^M - 1. (e.g. 1-bit is 1 (2^1 - 1), 2-bit is 3 (2^2 - 1))
        // Need lemma for max value of Str2Int(s)
    }
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
    // inductive proof on k
    if k == 0 {
        assert (Str2Int(s1) >= (1u64 << (s1.len() - 1)) as nat);
        assert (Str2Int(s2) < (1u64 << (s1.len() - 1)) as nat);
        assert (Str2Int(s1) > Str2Int(s2));
    } else {
        let s1_prefix = s1.subrange(0, k as int);
        let s2_prefix = s2.subrange(0, k as int);
        let s1_suffix = s1.subrange(k as int + 1, s1.len() as int);
        let s2_suffix = s2.subrange(k as int + 1, s2.len() as int);

        assert(Str2Int(s1) == 2 * Str2Int(s1.subrange(0, k as int)) + (if s1@[k] == '1' { 1nat } else { 0nat }) + /* rest */ 0);
        assert(Str2Int(s2) == 2 * Str2Int(s2.subrange(0, k as int)) + (if s2@[k] == '1' { 1nat } else { 0nat }) + /* rest */ 0);

        // The mathematical property required: if two numbers have the same prefix up to k, and the k-th digit of A is 1 and B is 0, A > B
        // Str2Int(s1) = (Str2Int(s1.subrange(0, k)) * 2 + s1[k]) * 2^(s1.len() - k - 1) + Str2Int(s1.subrange(k+1, s1.len()))
        // this is difficult using the current Str2Int definition.
        // The definition is essentially most significant bit first. No, it's least significant bit first.
        // Str2Int(s) = sum_{i=0}^{len-1} s[i]*2^i
        // So the current recursive definition is for little-endian.

        // Let's re-state the property:
        // Str2Int(s) = s[0]*2^0 + s[1]*2^1 + ... + s[len-1]*2^(len-1)
        // s1[j] == s2[j] for j < k
        // s1[k] == '1', s2[k] == '0'

        // Str2Int(s1) = sum_{j=0}^{k-1} s1[j]*2^j + s1[k]*2^k + sum_{j=k+1}^{s1.len()-1} s1[j]*2^j
        // Str2Int(s2) = sum_{j=0}^{k-1} s2[j]*2^j + s2[k]*2^k + sum_{j=k+1}^{s2.len()-1} s2[j]*2^j

        // Since s1[j] == s2[j] for j < k, the first sums are equal.
        // s1[k]*2^k = 1*2^k = 2^k
        // s2[k]*2^k = 0*2^k = 0

        // We need to show: 2^k + sum_{j=k+1}^{s1.len()-1} s1[j]*2^j > sum_{j=k+1}^{s2.len()-1} s2[j]*2^j
        // We know that sum_{j=k+1}^{s2.len()-1} s2[j]*2^j <= sum_{j=k+1}^{s1.len()-1} '1'*2^j for all '1's at s2's higher places.
        // Max value of the right part = 2^(s1.len()) - 2^(k+1)
        // We need to show 2^k > max possible value of right part of S2 minus min possible value of right part of S1+2^k.

        let remaining_length = s1.len() - (k + 1) as int;
        // Max value of sum_{j=k+1}^{s1.len()-1} s2[j]*2^j is sum_{j=k+1}^{s1.len()-1} 1*2^j, which is 2^(s1.len()) - 2^(k+1)
        // Str2Int(s1.subrange(k+1, s1.len())) * 2^(k+1)
        // Str2Int(s2.subrange(k+1, s2.len())) * 2^(k+1)

        // The definition of Str2Int is little-endian, so s[0] is LSB.
        // Str2Int(s) = sum_{i=0}^{len-1} s[i] * 2^i

        // Let P = sum_{i=0}^{k-1} s1[i] * 2^i = sum_{i=0}^{k-1} s2[i] * 2^i
        // Let R1 = sum_{i=k+1}^{s1.len()-1} s1[i] * 2^i
        // Let R2 = sum_{i=k+1}^{s2.len()-1} s2[i] * 2^i

        // Str2Int(s1) = P + 1 * 2^k + R1
        // Str2Int(s2) = P + 0 * 2^k + R2 = P + R2

        // We need to show P + 2^k + R1 > P + R2, or 2^k + R1 > R2
        // We know R2 <= sum_{i=k+1}^{s2.len()-1} 1 * 2^i = (2^(s2.len()) - 2^(k+1))

        // Is R2 < 2^k possible? No, if s2.len() > k+1. It's actually possible.
        // R2 = Str2Int(s2.subrange(k+1, s2.len())) * 2^(k+1);

        // The largest value that R2 can take is when all subsequent bits are '1'.
        // max(R2) = (2^(s2.len() - (k+1))) * 2^(k+1) - 2^(k+1)  ??? No
        // max(R2) = sum_{j=k+1}^{s1.len()-1} 2^j = 2^(s1.len()) - 2^(k+1)

        // We need to show: 2^k + R1 > max(R2)
        // This means 2^k > max(R2) - R1. Since R1 >= 0, this gets harder.
        // Rather, 2^k + R1 > R2. Since R1 >= 0, we can say 2^k > R2 - R1.
        // If R2 - R1 <= 0, then 2^k +0 > 0, done.
        // If R2 - R1 > 0, then we need to ensure 2^k > R2 - R1.

        // Max possible value of R2 is (1 << (s1.len() - (k+1))) * (1 << (k+1)) - (1 << (k+1)) = (1 << s1.len()) - (1 << (k+1))
        // No, this is easier: max value of sum_{j=k+1}^{s1.len()-1} 1 * 2^j is 2^(s1.len()) - 2^(k+1)

        // Proof by induction using the recursive definition of Str2Int.
        // Let L1 = s1.len(), L2 = s2.len()
        // L1 == L2
        // s1[L1-1] == s2[L1-1] unless k == L1-1
        // if k == L1-1 (last digit differs)
        // Str2Int(s1) = 2*Str2Int(s1.subrange(0, L1-1)) + 1
        // Str2Int(s2) = 2*Str2Int(s2.subrange(0, L1-1)) + 0
        // By inductive hypothesis, Str2Int(s1.subrange(0, L1-1)) == Str2Int(s2.subrange(0, L1-1))
        // So Str2Int(s1) > Str2Int(s2)

        // if k < L1-1 (some digit before last differs)
        // Str2Int(s1) = 2*Str2Int(s1.subrange(0, L1-1)) + (s1[L1-1] == '1' ? 1 : 0)
        // Str2Int(s2) = 2*Str2Int(s2.subrange(0, L1-1)) + (s2[L1-1] == '1' ? 1 : 0)
        // We know s1[L1-1] == s2[L1-1] from the prefix match unless k == L1-1
        // No, this approach using the recursive definition is tricky because Str2Int is least significant bit first.
        // The indices passed to `subrange` are (`start`, `end_exclusive`).
        // `Str2Int(s.subrange(0, s.len() as int - 1))` is the number represented by the first `len - 1` bits.
        // `s.index(s.len() as int - 1)` is the most significant bit.

        // Ok, the definition is MOST significant bit first.
        // s[0] is the MSB.
        // Str2Int(s) = s[0]*2^(len-1) + s[1]*2^(len-2) + ... + s[len-1]*2^0

        // Recursive definition: Str2Int(s) = 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
        // This means s.index(s.len() as int - 1) is the LSB.
        // This is important.
        // So, k in `s1@[k] == '1', s2@[k] == '0'` refers to the k-th most significant bit, NOT the k-th least significant bit.
        // Let's re-index `k` to be the index from the LSB.
        // `real_k = s1.len() - 1 - k` where `k` is from the function argument.

        // Let's assume the current `k` is the index from the MSB, so `s1[k]` is the first differing bit from the left.
        if k == 0 {
            // s1[0] == '1', s2[0] == '0'
            // And others are same up to comparison function
            assert(s1@[0] == '1');
            assert(s2@[0] == '0');
            assert(s1.len() == s2.len());
            let len = s1.len();
            if len > 0 {
                // Str2Int is little endian. s.index(0) is LSB.
                // The problem text implies s[0] is MSB, but the Str2Int definition implies s[len-1] is LSB.
                // Let's use the definition of Str2Int as given, which is LSB at s[len-1].
                // So, s[len-1] is LSB, s[0] is MSB based on current interpretation.
                // No, the Verus Str2Int is: `s.index(s.len() as int - 1)` is the LSB position, `Str2Int(s.subrange(0, s.len() as int - 1))` is higher bits contribution.
                // It means: s[len-1] is the coefficient of 2^0, s[len-2] is coeff of 2^1, ..., s[0] is coeff of 2^(len-1).

                // So, the function argument `k` (the first differing bit) is an index from the MSB.
                // If k=0, then s1[0] differs from s2[0].
                // My `Str2Int_inequality_by_first_diff` should ensure that the higher bits are equal.
                // So, `s1.len() - 1 - k` would be the power of 2 for this position.

                // If k=0, this is the most significant bit. s1[0] = '1', s2[0] = '0'.
                // Power for position `k` is `s.len() - 1 - k`.

                // Sums of powers:
                // Str2Int(s1) = sum_{j=0}^{s1.len()-1} (if s1[j]=='1' {1} else {0}) * 2^(s1.len()-1-j)
                // Str2Int(s2) = sum_{j=0}^{s2.len()-1} (if s2[j]=='1' {1} else {0}) * 2^(s2.len()-1-j)

                // For j < k, s1[j] == s2[j]. So terms for j < k are equal.
                // At j == k:
                // s1[k] gives 1*2^(s1.len()-1-k)
                // s2[k] gives 0*2^(s2.len()-1-k)

                // For j > k:
                // R1 = sum_{j=k+1}^{s1.len()-1} (if s1[j]=='1' {1} else {0}) * 2^(s1.len()-1-j)
                // R2 = sum_{j=k+1}^{s2.len()-1} (if s2[j]=='1' {1} else {0}) * 2^(s2.len()-1-j)

                // We need to show: 2^(s1.len()-1-k) + R1 > R2
                // Max possible R2 is sum_{j=k+1}^{s1.len()-1} 1 * 2^(s1.len()-1-j)
                // This sum is 2^(s1.len()-(k+1)) - 1. (e.g., if k+1=len-1, then 2^1 - 1 = 1, just 2^0)
                // No, sum_{i=0}^{N-1} 2^i = 2^N - 1
                // Let p = s1.len()-1-j
                // When j=k+1, p = s1.len()-1-(k+1) = s1.len()-k-2
                // When j=s1.len()-1, p = s1.len()-1-(s1.len()-1) = 0
                // So max(R2) = sum_{p=0}^{s1.len()-k-2} 2^p = 2^(s1.len()-k-1) - 1.

                // So we need to show: 2^(s1.len()-1-k) + R1 > max(R2).
                // We need to show: 2^(s1.len()-1-k) + R1 > (2^(s1.len()-k-1) - 1)
                // Since R1 >= 0, it reduces to: 2^(s1.len()-1-k) > 2^(s1.len()-k-1) - 1
                // Which is 2^(s1.len()-k-1) > 2^(s1.len()-k-1) - 1, which is true.
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
        // Lengths are equal, perform bitwise comparison
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



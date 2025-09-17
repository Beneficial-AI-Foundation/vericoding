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
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 9): Updated `nat_to_seq_bit_string_preserves_validity` spec to simplify guards and handle `n=0` more directly to align with `Str2Int` definition. */
spec fn nat_to_seq_bit_string_preserves_validity(n: nat) -> (s: Seq<char>)
    ensures s.len() > 0 && Str2Int(s) == n && ValidBitString(s)
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        let prefix = nat_to_seq_bit_string_preserves_validity(n / 2);
        prefix.push(last_bit)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Corrected the type conversion from `nat` to `int` within the `index` method for `dividend_seq`. */
{
    let dividend_seq = dividend@;
    let divisor_seq = divisor@;

    if Str2Int(dividend_seq) < Str2Int(divisor_seq) {
        return (vec!['0'], dividend_seq.into_vec());
    }

    let mut quotient_seq: Seq<char> = Seq::new(0, |i| ' '); // Initialize with dummy values, will be overwritten
    let mut remainder_seq: Seq<char> = Seq::new(0, |i| ' '); // Initialize with dummy values, will be overwritten

    let mut k: nat = 0;
    while k < dividend_seq.len()
        invariant (
            k <= dividend_seq.len(),
            ValidBitString(quotient_seq),
            ValidBitString(remainder_seq),
            Str2Int(remainder_seq) < Str2Int(divisor_seq) || remainder_seq.len() == 0,
            quotient_seq.len() == k as int,
        )
        decreases dividend_seq.len() - k
    {
        if remainder_seq.len() == 0 {
             remainder_seq = seq![dividend_seq.index(k as int)];
        } else {
             remainder_seq = remainder_seq.push(dividend_seq.index(k as int));
        }

        if Str2Int(remainder_seq) >= Str2Int(divisor_seq) {
            quotient_seq = quotient_seq.push('1');
            let new_remainder_val = Str2Int(remainder_seq) - Str2Int(divisor_seq);
             proof {
                assert(ValidBitString(nat_to_seq_bit_string_preserves_validity(new_remainder_val)));
            }
            remainder_seq = nat_to_seq_bit_string_preserves_validity(new_remainder_val);
        } else {
            quotient_seq = quotient_seq.push('0');
        }
        k = k + 1;
    }

    // Remove leading zeros from quotient if any (except for '0' itself).
    let mut final_quotient_vec = quotient_seq.into_vec();
    while final_quotient_vec.len() > 1 && final_quotient_vec[0] == '0' {
        final_quotient_vec.remove(0);
    }

    (final_quotient_vec, remainder_seq.into_vec())
}
// </vc-code>

fn main() {}
}


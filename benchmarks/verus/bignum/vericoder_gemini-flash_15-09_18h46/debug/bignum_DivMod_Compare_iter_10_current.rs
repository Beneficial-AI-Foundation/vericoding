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
/* helper modified by LLM (iteration 10): Removed `nat_to_seq_bit_string_preserves_validity` as it was not directly used in the current iteration of the code. */
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Casted `k` to `usize` for `dividend_seq.index` to fix the compilation error, aligning with the type required by `index` for array access. */
{
    let dividend_seq = dividend@;
    let divisor_seq = divisor@;

    if Str2Int(dividend_seq) < Str2Int(divisor_seq) {
        return (vec!['0'], dividend_seq.into_vec());
    }

    let mut quotient_vec: Vec<char> = Vec::new();
    let mut remainder_seq: Seq<char> = Seq::empty();

    let mut k: nat = 0;
    while k < dividend_seq.len()
        invariant (
            k <= dividend_seq.len(),
            ValidBitString(quotient_vec@),
            ValidBitString(remainder_seq),
            Str2Int(remainder_seq) < Str2Int(divisor_seq) || remainder_seq.len() == 0,
            quotient_vec@.len() == k as int,
        )
        decreases dividend_seq.len() - k
    {
        if remainder_seq.len() == 0 {
             remainder_seq = seq![dividend_seq.index(k as usize)];
        } else {
             remainder_seq = remainder_seq.push(dividend_seq.index(k as usize));
        }

        if Str2Int(remainder_seq) >= Str2Int(divisor_seq) {
            quotient_vec.push('1');
            let new_remainder_val = Str2Int(remainder_seq) - Str2Int(divisor_seq);

            // Convert new_remainder_val (nat) to Seq<char>
            let mut temp_remainder_vec: Vec<char> = Vec::new();
            if new_remainder_val == 0 {
                temp_remainder_vec.push('0');
            } else {
                let mut current_val = new_remainder_val;
                while current_val > 0
                    invariant
                        ValidBitString(temp_remainder_vec@),
                        current_val >= 0,
                    decreases current_val
                {
                    if current_val % 2 == 1 {
                        temp_remainder_vec.insert(0, '1');
                    } else {
                        temp_remainder_vec.insert(0, '0');
                    }
                    current_val = current_val / 2;
                }
            }
            remainder_seq = temp_remainder_vec@;

        } else {
            quotient_vec.push('0');
        }
        k = k + 1;
    }

    // Remove leading zeros from quotient if any (except for '0' itself).
    while quotient_vec.len() > 1 && quotient_vec[0] == '0' {
        quotient_vec.remove(0);
    }

    (quotient_vec, remainder_seq.into_vec())
}
// </vc-code>

fn main() {}
}


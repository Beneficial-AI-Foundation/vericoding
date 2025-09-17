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
spec fn Ge(a: Seq<char>, b: Seq<char>) -> bool {
    if a.len() > b.len() { return true; }
    if a.len() < b.len() { return false; }
    forall |i: int| 0 <= i && i < a.len() as int ==> (a.index(i) == b.index(i) || a.index(i) == '1' && b.index(i) == '0')
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let dividend_seq = dividend@;
    let divisor_seq = divisor@;

    let mut quotient = Vec::<char>::new();
    let mut remainder = Vec::<char>::new();

    let mut i = 0;
    while i < dividend_seq.len() {
        invariant {
            i <= dividend_seq.len(),
            ValidBitString(quotient@),
            ValidBitString(remainder@),
            Str2Int(remainder@) < Str2Int(divisor_seq),
            Str2Int(remainder@) + Str2Int(quotient@) * Str2Int(divisor_seq) == Str2Int(dividend_seq.subrange(0, i as int)),
        }

        remainder.push(dividend_seq.index(i as int));

        if Str2Int(remainder@) >= Str2Int(divisor_seq) {
            quotient.push('1');
            let rem_int = Str2Int(remainder@);
            let div_int = Str2Int(divisor_seq);

            // Subtraction logic (bit by bit)
            let mut temp_remainder_vec = Vec::<char>::new();
            let mut borrow = false;
            let mut j = remainder.len() as int - 1;
            let mut k = divisor_seq.len() as int - 1;

            while j >= 0 {
                invariant {
                    j >= -1,
                    ValidBitString(temp_remainder_vec@),
                    remainder.len() == temp_remainder_vec.len() + (remainder.len() - (j + 1) as int),
                }
                let r_bit = if remainder.index(j as int) == '1' { 1 } else { 0 };
                let d_bit = if k >= 0 && divisor_seq.index(k as int) == '1' { 1 } else { 0 };

                let current_r = r_bit - (if borrow { 1 } else { 0 });

                if current_r < d_bit {
                    temp_remainder_vec.insert(0, (if current_r + 2 - d_bit == 1 { '1' } else { '0' }));
                    borrow = true;
                } else {
                    temp_remainder_vec.insert(0, (if current_r - d_bit == 1 { '1' } else { '0' }));
                    borrow = false;
                }
                j = j - 1;
                k = k - 1;
            }
            remainder = temp_remainder_vec;

            // Remove leading zeros from remainder
            while remainder.len() > 1 && remainder.index(0) == '0' {
                remainder.remove(0);
            }
        } else {
            quotient.push('0');
        }
        i = i + 1;
    }

    // Remove leading zeros from quotient if it's not "0" itself
    while quotient.len() > 1 && quotient.index(0) == '0' {
        quotient.remove(0);
    }
    if quotient.len() == 0 {
        quotient.push('0');
    }

    (quotient, remainder)
}
// </vc-code>

fn main() {}
}


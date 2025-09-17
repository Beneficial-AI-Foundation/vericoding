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
spec fn Str2Int(s: Seq<char>) -> nat recommends ValidDigitString(s) { if s.len() == 0 { 0 } else { 2 * Str2Int(s.drop_last()) + (if s.last() == option_helper_char_1() { 1nat } else { 0nat }) } } proof fn option_helper_char_1() -> char { '1' } proof fn option_helper_char_0() -> char { '0' } spec fn ValidDigitString(s: Seq<char>) -> bool { forall |i: int| 0 <= i && i < s.len() ==> (s.index(i) == option_helper_char_0() || s.index(i) == option_helper_char_1()) }
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let dividend_seq = dividend@;
    let divisor_seq = divisor@;

    if Str2Int(dividend_seq) < Str2Int(divisor_seq) {
        return (Vec::<char>::new(), dividend_seq.to_vec());
    }

    let mut quotient_seq: Seq<char> = Seq::new();
    let mut remainder_seq: Seq<char> = Seq::new();

    let mut k = 0;
    while k < dividend_seq.len()
        invariant
            0 <= k && k <= dividend_seq.len(),
            ValidDigitString(quotient_seq),
            ValidDigitString(remainder_seq),
            Str2Int(remainder_seq) < Str2Int(divisor_seq) || remainder_seq.len() == 0,
            Str2Int(quotient_seq) * Str2Int(divisor_seq) + Str2Int(remainder_seq) == Str2Int(dividend_seq.subrange(0, k as int)),
    {
        remainder_seq = remainder_seq.push(dividend_seq.index(k as int));

        if Str2Int(remainder_seq) >= Str2Int(divisor_seq) {
            quotient_seq = quotient_seq.push('1');
            remainder_seq = (Str2Int(remainder_seq) - Str2Int(divisor_seq)).to_seq_bit_string();
        } else {
            quotient_seq = quotient_seq.push('0');
        }
        k = k + 1;
    }

    return (quotient_seq.to_vec(), remainder_seq.to_vec());
}
// </vc-code>

fn main() {}
}


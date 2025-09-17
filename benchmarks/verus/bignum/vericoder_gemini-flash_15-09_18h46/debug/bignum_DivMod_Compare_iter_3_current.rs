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
/* helper modified by LLM (iteration 3): Removed unused helpers, fixed ValidBitString to match spec for consistency */
spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

spec fn nat_to_seq_bit_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        nat_to_seq_bit_string(n / 2).push(last_bit)
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
/* code modified by LLM (iteration 3): Fixed indexing type issue */
{
    let dividend_seq = dividend@;
    let divisor_seq = divisor@;

    if Str2Int(dividend_seq) < Str2Int(divisor_seq) {
        return (Vec::<char>::new(), dividend_seq.to_vec());
    }

    let mut quotient_seq: Seq<char> = Seq::new();
    let mut remainder_seq: Seq<char> = Seq::new();

    let mut k: int = 0;
    while k < dividend_seq.len()
        invariant
            0 <= k && k <= dividend_seq.len(),
            ValidBitString(quotient_seq),
            ValidBitString(remainder_seq),
            Str2Int(remainder_seq) < Str2Int(divisor_seq) || remainder_seq.len() == 0,
            // Str2Int(remainder_seq) <= Str2Int(dividend_seq.subrange(0, k as int)), // This invariant needs careful re-evaluation
            ValidBitString(dividend_seq.subrange(0,k as int)),
        decreases dividend_seq.len() - k
    {
        remainder_seq = remainder_seq.push(dividend_seq.index(k));

        if Str2Int(remainder_seq) >= Str2Int(divisor_seq) {
            quotient_seq = quotient_seq.push('1');
            let new_remainder_val = Str2Int(remainder_seq) - Str2Int(divisor_seq);
            remainder_seq = nat_to_seq_bit_string(new_remainder_val);
        } else {
            quotient_seq = quotient_seq.push('0');
        }
        k = k + 1;
    }

    (quotient_seq.to_vec(), remainder_seq.to_vec())
}
// </vc-code>

fn main() {}
}


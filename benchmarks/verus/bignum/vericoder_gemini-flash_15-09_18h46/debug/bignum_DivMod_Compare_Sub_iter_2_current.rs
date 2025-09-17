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
/* helper modified by LLM (iteration 2): Adds int_to_bit_string function to convert nat to Seq<char> */
spec fn int_to_bit_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        if n / 2 == 0 {
            seq![last_bit]
        } else {
            int_to_bit_string(n / 2).push_front(last_bit)
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod_Compare_Sub(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Initialize variables and call helper for bit string conversion */
{
  let n = Str2Int(dividend@);
  let d = Str2Int(divisor@);

  let quotient_nat = n / d;
  let remainder_nat = n % d;

  let quotient_vec = int_to_bit_string(quotient_nat).to_vec();
  let remainder_vec = int_to_bit_string(remainder_nat).to_vec();

  (quotient_vec, remainder_vec)
}
// </vc-code>

fn main() {}
}


// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
fn nat_to_vec_char_binary(n: nat) -> (result: Vec<char>)
    ensures valid_bit_string(result@)
{
    let mut chars: Vec<char> = Vec::new();
    if n == 0 {
        chars.push('0');
        return chars;
    }

    let mut temp_n: nat = n;
    while temp_n > 0
        invariant
            temp_n.to_int() >= 0,
            valid_bit_string(chars@),
        decreases temp_n
    {
        let digit = (temp_n % 2) as nat; // Cast result of % to nat
        if digit == 0 {
            chars.push('0');
        } else {
            chars.push('1');
        }
        temp_n = temp_n / 2;
    }
    chars.reverse();
    chars
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0,
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
{
    let dividend_val: nat = str2int(dividend@);
    let divisor_val: nat = str2int(divisor@);

    let quotient_val: nat = dividend_val / divisor_val;
    let remainder_val: nat = dividend_val % divisor_val;

    let quotient_vec = nat_to_vec_char_binary(quotient_val);
    let remainder_vec = nat_to_vec_char_binary(remainder_val);

    (quotient_vec, remainder_vec)
}
// </vc-code>


}

fn main() {}
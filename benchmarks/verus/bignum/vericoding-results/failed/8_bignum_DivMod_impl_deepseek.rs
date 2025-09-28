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
/* helper modified by LLM (iteration 10): Removed u64 conversion and used vector operations */
proof fn lemma_div_mod_properties(quotient: Vec<char>, remainder: Vec<char>, divisor: Vec<char>, dividend: Vec<char>)
  requires
    valid_bit_string(quotient@) && valid_bit_string(remainder@) && valid_bit_string(divisor@) && valid_bit_string(dividend@),
    str2int(divisor@) > 0,
    str2int(remainder@) < str2int(divisor@),
    str2int(quotient@) * str2int(divisor@) + str2int(remainder@) == str2int(dividend@),
  ensures
    str2int(quotient@) == str2int(dividend@) / str2int(divisor@),
    str2int(remainder@) == str2int(dividend@) % str2int(divisor@),
{
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
/* code modified by LLM (iteration 10): Avoid reverse() operation and build bits directly in correct order */
{
    let mut quotient: Vec<char> = Vec::new();
    let mut current_value: nat = 0;
    
    let mut i: int = 0;
    while i < dividend.len() as int
        invariant
            0 <= i <= dividend.len() as int,
            valid_bit_string(quotient@),
            current_value == str2int(dividend@.subrange(0, i)) % str2int(divisor@),
            str2int(quotient@) * str2int(divisor@) + current_value == str2int(dividend@.subrange(0, i)),
    {
        let current_bit = dividend[i as usize];
        current_value = current_value * 2 + (if current_bit == '1' { 1 } else { 0 });
        
        if current_value >= str2int(divisor@) {
            quotient.push('1');
            current_value = current_value - str2int(divisor@);
        } else {
            quotient.push('0');
        }
        i = i + 1;
    }
    
    let mut rem_bits: Vec<char> = Vec::new();
    let mut temp_remainder = current_value;
    let mut bits: Vec<char> = Vec::new();
    
    if temp_remainder == 0 {
        bits.push('0');
    } else {
        while temp_remainder > 0
            invariant
                valid_bit_string(bits@),
                str2int(bits@) == temp_remainder,
        {
            if temp_remainder % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            temp_remainder = temp_remainder / 2;
        }
        let mut j = bits.len() - 1;
        while j >= 0
            invariant
                valid_bit_string(rem_bits@),
                str2int(rem_bits@) == str2int(bits@.subrange(j + 1, bits.len() as int)),
        {
            rem_bits.push(bits[j]);
            if j > 0 {
                j = j - 1;
            } else {
                break;
            }
        }
    }
    
    proof {
        lemma_div_mod_properties(quotient.clone(), rem_bits.clone(), divisor.clone(), dividend.clone());
    }
    
    (quotient, rem_bits)
}
// </vc-code>


}

fn main() {}
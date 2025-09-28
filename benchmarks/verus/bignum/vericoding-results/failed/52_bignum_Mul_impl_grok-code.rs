// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
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

// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed compilation errors by removing invalid 'int' suffixes from literals */
    let len1: usize = s1.len();
    let len2: usize = s2.len();
    if len1 == 0 || len2 == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    let mut sum_bits: Vec<int> = Vec::new();
    for _ in 0..len1 + len2 {
        sum_bits.push(0);
    }
    for j in 0..len2 {
        let bit2 = if s2[len2 - 1 - j] == '1' { 1 } else { 0 };
        if bit2 == 1 {
            let mut carry = 0;
            for k in 0..len1 {
                let bit1 = if s1[len1 - 1 - k] == '1' { 1 } else { 0 };
                let idx = j + k;
                let current = sum_bits[idx];
                let new_sum = bit1 + current + carry;
                sum_bits[idx] = new_sum % 2;
                carry = new_sum / 2;
            }
            let mut idx = j + len1;
            while carry > 0 && idx < len1 + len2
                invariant
                    carry == 0 || carry == 1,
                    0 <= idx as int && idx as int <= (len1 as int + len2 as int)
                decreases (len1 as int + len2 as int - idx as int)
            {
                let current = sum_bits[idx];
                let new_sum = current + carry;
                sum_bits[idx] = new_sum % 2;
                carry = new_sum / 2;
                idx += 1;
            }
        }
    }
    let mut result = Vec::new();
    let mut found = false;
    for i in 0..len1 + len2 {
        let p = len1 + len2 - 1 - i;
        let bit = sum_bits[p];
        if found || bit != 0 {
            found = true;
            result.push(if bit == 1 { '1' } else { '0' });
        }
    }
    if result.len() == 0 {
        result.push('0');
    }
    result
}
// </vc-code>


}

fn main() {}
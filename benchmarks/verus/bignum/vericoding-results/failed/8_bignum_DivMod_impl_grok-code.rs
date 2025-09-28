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
/* helper modified by LLM (iteration 10): replaced i += 1 with i = i + 1 to fix compilation error with int type in proof fn */

proof fn bit_geq(a: &Vec<char>, b: &Vec<char>) -> (result: bool)
    requires
        valid_bit_string(a@) && valid_bit_string(b@),
    ensures
        result <==> str2int(a@) >= str2int(b@),
{
    let len_a = a@.len();
    let len_b = b@.len();
    if len_a > len_b {
        true
    } else if len_b > len_a {
        false
    } else {
        let mut i: int = 0;
        assert(i <= len_a);
        while i < len_a && a@[i] == b@[i] 
            invariant
                0 <= i <= len_a,
                forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        {
            i = i + 1;
            assert(i <= len_a);
        }
        if i == len_a {
            true
        } else {
            a@[i] > b@[i]
        }
    }
}

fn normalize(s: Vec<char>) -> (result: Vec<char>)
    requires
        valid_bit_string(s@),
    ensures
        valid_bit_string(result@),
        str2int(result@) == str2int(s@),
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len() && s[i] == '0' {
        i += 1;
    }
    if i == s.len() {
        result.push('0');
    } else {
        while i < s.len() {
            result.push(s[i]);
            i += 1;
        }
    }
    result
}

fn subtract(a: Vec<char>, b: Vec<char>) -> (result: Vec<char>)
    requires
        valid_bit_string(a@) && valid_bit_string(b@),
        str2int(a@) >= str2int(b@),
    ensures
        valid_bit_string(result@),
        str2int(result@) == str2int(a@) - str2int(b@),
{
    let len1 = a.len();
    let len2 = b.len();
    let max_len: usize = if len1 > len2 { len1 } else { len2 };
    let mut a_padded: Vec<char> = Vec::new();
    let mut b_padded: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < (max_len - len1) {
        a_padded.push('0');
        i += 1;
    }
    i = 0;
    while i < len1 {
        a_padded.push(a[i]);
        i += 1;
    }
    i = 0;
    while i < (max_len - len2) {
        b_padded.push('0');
        i += 1;
    }
    i = 0;
    while i < len2 {
        b_padded.push(b[i]);
        i += 1;
    }
    let mut result: Vec<char> = Vec::new();
    let mut borrow = false;
    let mut i: usize = max_len;
    while i > 0 {
        i -= 1;
        let aa = if a_padded[i] == '1' { 1 } else { 0 };
        let bb = if b_padded[i] == '1' { 1 } else { 0 };
        let sub = aa - bb - (if borrow { 1 } else { 0 });
        let bit = if sub >= 0 { sub } else { sub + 2 };
        borrow = sub < 0;
        result.insert(0, if bit == 1 { '1' } else { '0' });
    }
    normalize(result)
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
    /* code modified by LLM (iteration 10): implemented binary division algorithm using helpers */
    let dividend_norm = normalize(dividend);
    let divisor_norm = normalize(divisor);
    if divisor_norm.len() == 0 || (divisor_norm.len() == 1 && divisor_norm[0] == '0') || dividend_norm.len() == 0 {
        (vec!['0'], vec!['0'])
    } else if !bit_geq(&dividend_norm, &divisor_norm) {
        (vec!['0'], dividend_norm)
    } else {
        let mut remainder: Vec<char> = Vec::new();
        let mut idx: usize = 0;
        while idx < divisor_norm.len() {
            remainder.push(dividend_norm[idx]);
            idx += 1;
        }
        let mut quotient: Vec<char> = Vec::new();
        let mut idx: usize = divisor_norm.len();
        while idx < dividend_norm.len() {
            remainder.push(dividend_norm[idx]);
            remainder = normalize(remainder);
            if bit_geq(&remainder, &divisor_norm) {
                quotient.push('1');
                remainder = subtract(remainder, divisor_norm.clone());
            } else {
                quotient.push('0');
            }
            idx += 1;
        }
        let quotient_norm = normalize(quotient);
        let remainder_norm = normalize(remainder);
        (quotient_norm, remainder_norm)
    }
}
// </vc-code>


}

fn main() {}
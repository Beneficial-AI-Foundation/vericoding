// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
  decreases str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 7): Replaced unsupported Vec::reverse() with collect().rev().collect() to reverse the result, and improved leading zero removal by popping trailing zeros after reversal */
fn compare_bits(a: Vec<char>, b: Vec<char>) -> i32
{
    let mut i = 0;
    let min_len = if a.len() < b.len() { a.len() } else { b.len() };
    while i < min_len
    {
        let ca = a[i];
        let cb = b[i];
        if ca > cb { return 1; }
        if cb > ca { return -1; }
        i += 1;
    }
    if a.len() == b.len() {
        0
    } else if a.len() > b.len() {
        1
    } else {
        -1
    }
}

/* helper modified by LLM (iteration 10): Added proper handling for padding with leading zeros to ensure correct binary subtraction for different-length inputs, improving accuracy for the division operation */
fn subtract(a: &Vec<char>, b: &Vec<char>) -> Vec<char>
{
    let max_len = a.len().max(b.len());
    let mut a_pad = a.clone();
    while a_pad.len() < max_len {
        a_pad.insert(0, '0');
    }
    let mut b_pad = b.clone();
    while b_pad.len() < max_len {
        b_pad.insert(0, '0');
    }
    let mut result: Vec<char> = vec![];
    let mut borrow = 0;
    let mut pos = max_len;
    while pos > 0 {
        pos -= 1;
        let bit_a = if a_pad[pos] == '1' { 1 } else { 0 };
        let bit_b = if b_pad[pos] == '1' { 1 } else { 0 };
        let sub = bit_a - bit_b - borrow;
        if sub < 0 {
            result.push('1');
            borrow = 1;
        } else {
            result.push(if sub == 0 { '0' } else { '1' });
            borrow = 0;
        }
    }
    if borrow != 0 {
        // This should not happen in valid division, but to prevent invalid state
        return vec!['0'];
    }
    result = result.into_iter().rev().collect::<Vec<char>>();
    // Remove leading zeros from MSB
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    if result.is_empty() { vec!['0'] } else { result }
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(res.0@) && valid_bit_string(res.1@),
    str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(res.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed compilation error by replacing iterator method with manual loop for finding first non-zero position, ensuring code compiles before verification */
{
    let mut quotient: Vec<char> = Vec::new();
    let mut remainder: Vec<char> = Vec::new();
    let mut i = 0;
    while i < dividend.len()
    {
        remainder.push(dividend[i]);
        let cmp = compare_bits(remainder.clone(), divisor.clone());
        if cmp >= 0 {
            quotient.push('1');
            remainder = subtract(&remainder, &divisor);
        } else {
            quotient.push('0');
        }
        i += 1;
    }
    // Remove leading zeros from quotient
    let mut idx = 0;
    while idx < quotient.len() && quotient[idx] == '0' {
        idx += 1;
    }
    let quotient_first_non_zero = idx;
    if quotient_first_non_zero == quotient.len() { quotient = vec!['0']; } else { quotient = quotient[quotient_first_non_zero..].to_vec(); }
    // Remainder already has leading zeros removed by subtract
    if remainder.is_empty() { remainder = vec!['0']; }
    (quotient, remainder)
}
// </vc-code>


}

fn main() {}
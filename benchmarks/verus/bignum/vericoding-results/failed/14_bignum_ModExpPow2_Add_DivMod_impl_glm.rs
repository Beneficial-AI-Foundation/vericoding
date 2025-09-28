// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) && str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replaced rev().collect() with manual reversal */
fn add_binary(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
{
    let mut carry = 0;
    let mut result = Vec::new();
    let max_len = a.len().max(b.len());
    for i in 0..max_len {
        let a_bit = if i < a.len() { a[a.len() - 1 - i] } else { '0' };
        let b_bit = if i < b.len() { b[b.len() - 1 - i] } else { '0' };
        let sum = carry + (if a_bit == '1' { 1 } else { 0 }) + (if b_bit == '1' { 1 } else { 0 });
        carry = sum / 2;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
    }
    if carry > 0 {
        result.push('1');
    }
    let mut reversed_result = Vec::new();
    for i in 0..result.len() {
        reversed_result.push(result[result.len() - 1 - i]);
    }
    reversed_result
}

fn mul_binary(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
{
    let mut result = vec!['0'];
    let mut b_shifted = b.clone();
    for i in 0..a.len() {
        if a[a.len() - 1 - i] == '1' {
            result = add_binary(result, b_shifted);
        }
        b_shifted.push('0');
    }
    result
}

fn compare_binary(a: Vec<char>, b: Vec<char>) -> (res: i32)
{
    if a.len() > b.len() {
        1
    } else if a.len() < b.len() {
        -1
    } else {
        for i in 0..a.len() {
            if a[i] > b[i] {
                return 1;
            } else if a[i] < b[i] {
                return -1;
            }
        }
        0
    }
}

/* helper modified by LLM (iteration 5): replaced rev().collect() with manual reversal */
fn subtract_binary(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
{
    let mut borrow = 0;
    let mut result = Vec::new();
    for i in 0..a.len() {
        let a_bit = if i < a.len() { a[a.len() - 1 - i] } else { '0' };
        let b_bit = if i < b.len() { b[b.len() - 1 - i] } else { '0' };
        let diff: i32 = (if a_bit == '1' { 1 } else { 0 }) - (if b_bit == '1' { 1 } else { 0 }) - borrow;
        borrow = if diff < 0 { 1 } else { 0 };
        let bit = if diff.abs() % 2 == 1 { '1' } else { '0' };
        result.push(bit);
    }
    let mut reversed_result = Vec::new();
    for i in 0..result.len() {
        reversed_result.push(result[result.len() - 1 - i]);
    }
    let mut start = 0;
    while start < reversed_result.len() - 1 && reversed_result[start] == '0' {
        start += 1;
    }
    reversed_result.drain(0..start);
    reversed_result
}

fn mod_binary(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
{
    let mut current = a;
    while compare_binary(current, b) >= 0 {
        current = subtract_binary(current, b);
    }
    current
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
    sy@.len() == n as int + 1 &&
    str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed helper functions to avoid complex iterator operations */
{
    if n == 0 {
        if sy[0] == '0' {
            vec!['1']
        } else {
            mod_binary(sx, sz)
        }
    } else {
        let mut result = sx;
        for _ in 0..n {
            result = mul_binary(result, result);
            result = mod_binary(result, sz);
        }
        result
    }
}
// </vc-code>


}

fn main() {}
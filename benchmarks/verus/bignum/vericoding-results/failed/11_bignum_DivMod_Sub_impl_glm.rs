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
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    str2int(s1) >= str2int(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 6): added assertion for length equality in ge function */
fn ge(a: &Vec<char>, b: &Vec<char>) -> bool {
    if a.len() > b.len() {
        true
    } else if a.len() < b.len() {
        false
    } else {
        assert(a.len() == b.len());
        for i in 0..a.len() {
            if a[i] > b[i] {
                return true;
            } else if a[i] < b[i] {
                return false;
            }
        }
        true
    }
}

/* helper modified by LLM (iteration 6): fixed index access to avoid underflow */
fn subtract_vectors(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    let n = if a.len() > b.len() { a.len() } else { b.len() };
    let mut result = Vec::new();
    result.reserve(n);
    for _ in 0..n {
        result.push('0');
    }
    let mut borrow = 0;

    for i in 0..n {
        let a_bit = if i < a.len() {
            let a_idx = a.len() - 1 - i;
            if a[a_idx] == '1' { 1 } else { 0 }
        } else {
            0
        };
        let b_bit = if i < b.len() {
            let b_idx = b.len() - 1 - i;
            if b[b_idx] == '1' { 1 } else { 0 }
        } else {
            0
        };

        let diff = a_bit - b_bit - borrow;
        if diff < 0 {
            borrow = 1;
            result[n - 1 - i] = if (diff + 2) % 2 == 1 { '1' } else { '0' };
        } else {
            borrow = 0;
            result[n - 1 - i] = if diff % 2 == 1 { '1' } else { '0' };
        }
    }

    result
}

/* helper modified by LLM (iteration 6): new function to remove leading zeros */
fn remove_leading_zeros(v: &mut Vec<char>) {
    while v.len() > 0 && v[0] == '0' {
        v.remove(0);
    }
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): added leading zeros removal and assertion for dividend access */
    let n = dividend.len();
    let m = divisor.len();

    let mut quotient = Vec::new();
    let mut remainder = Vec::new();

    for i in 0..n {
        assert(i < dividend.len());
        remainder.push(dividend[i]);
        remove_leading_zeros(&mut remainder);

        if ge(&remainder, &divisor) {
            quotient.push('1');
            remainder = subtract_vectors(remainder, divisor.clone());
            remove_leading_zeros(&mut remainder);
        } else {
            quotient.push('0');
        }
    }

    (quotient, remainder)
}
// </vc-code>


}

fn main() {}
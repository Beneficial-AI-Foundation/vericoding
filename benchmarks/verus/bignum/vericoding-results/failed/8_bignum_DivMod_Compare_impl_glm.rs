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
/* helper modified by LLM (iteration 2): fixed slicing compilation error */
fn vec_compare(a: &Vec<char>, b: &Vec<char>) -> (cmp: i32)
    ensures
        cmp == -1 ==> str2int(a@) < str2int(b@),
        cmp == 0 ==> str2int(a@) == str2int(b@),
        cmp == 1 ==> str2int(a@) > str2int(b@)
{
    let mut a_start = 0;
    while a_start < a.len() && a[a_start] == '0' {
        a_start += 1;
    }
    let a_len = a.len() - a_start;

    let mut b_start = 0;
    while b_start < b.len() && b[b_start] == '0' {
        b_start += 1;
    }
    let b_len = b.len() - b_start;

    if a_len > b_len {
        1
    } else if a_len < b_len {
        -1
    } else {
        let mut i = 0;
        while i < a_len {
            if a[a_start + i] > b[b_start + i] {
                return 1;
            } else if a[a_start + i] < b[b_start + i] {
                return -1;
            }
            i += 1;
        }
        0
    }
}

/* helper modified by LLM (iteration 5): changed second parameter to borrow to avoid move */
fn vec_subtract(a: Vec<char>, b: &Vec<char>) -> (res: Vec<char>)
    requires
        str2int(a@) >= str2int(b@)
    ensures
        str2int(res@) == str2int(a@) - str2int(b@),
        valid_bit_string(res@)
{
    let mut a_rev = Vec::new();
    for j in 0..a.len() {
        let i = a.len() - 1 - j;
        a_rev.push(a[i]);
    }
    let mut b_rev = Vec::new();
    for j in 0..b.len() {
        let i = b.len() - 1 - j;
        b_rev.push(b[i]);
    }

    let mut res_rev = Vec::new();
    let mut carry = 0;

    for i in 0..a_rev.len() {
        let a_bit = if a_rev[i] == '1' { 1 } else { 0 };
        let b_bit = if i < b_rev.len() && b_rev[i] == '1' { 1 } else { 0 };

        let diff = a_bit - b_bit - carry;
        if diff < 0 {
            carry = 1;
            res_rev.push(if diff + 2 == 1 { '1' } else { '0' });
        } else {
            carry = 0;
            res_rev.push(if diff == 1 { '1' } else { '0' });
        }
    }

    let mut res = Vec::new();
    for j in 0..res_rev.len() {
        let i = res_rev.len() - 1 - j;
        res.push(res_rev[i]);
    }

    let mut start = 0;
    while start < res.len() && res[start] == '0' {
        start += 1;
    }

    if start == res.len() {
        vec!['0']
    } else {
        let mut result = Vec::new();
        for i in start..res.len() {
            result.push(res[i]);
        }
        result
    }
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
{
    /* code modified by LLM (iteration 5): fixed borrow of moved divisor by using reference */
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();

    for i in 0..dividend.len() {
        remainder.push(dividend[i]);
        let cmp = vec_compare(&remainder, &divisor);
        if cmp >= 0 {
            remainder = vec_subtract(remainder, &divisor);
            quotient.push('1');
        } else {
            quotient.push('0');
        }
    }

    (quotient, remainder)
}
// </vc-code>


}

fn main() {}
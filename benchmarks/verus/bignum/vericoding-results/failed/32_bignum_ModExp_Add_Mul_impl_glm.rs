// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2_int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2_int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) + str2_int(s2),
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2_int(res) == str2_int(s1) * str2_int(s2),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added preconditions, postconditions, and loop with decreases clause */
fn is_zero(s: &Vec<char>) -> bool {
    if s.len() == 0 {
        true
    } else {
        let mut all_zeros = true;
        for i in 0..s.len() {
            if s[i] != '0' {
                all_zeros = false;
                break;
            }
        }
        all_zeros
    }
}

fn last_bit(s: Vec<char>) -> char {
    if s.len() == 0 {
        '0'
    } else {
        s[s.len()-1]
    }
}

fn shift_right(s: Vec<char>) -> Vec<char> {
    if s.len() == 0 {
        vec![]
    } else {
        let mut res = Vec::with_capacity(s.len()-1);
        for i in 0..s.len()-1 {
            res.push(s[i]);
        }
        res
    }
}

/* helper modified by LLM (iteration 4): replaced reversed range loops with forward loops */
fn add_bit_strings(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    let mut a_rev = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        a_rev.push(a[a.len() - 1 - i]);
    }
    let mut b_rev = Vec::with_capacity(b.len());
    for i in 0..b.len() {
        b_rev.push(b[b.len() - 1 - i]);
    }
    let mut carry = 0;
    let mut res_rev = Vec::new();
    let n = a_rev.len().max(b_rev.len());
    for i in 0..n {
        let bit_a = if i < a_rev.len() { if a_rev[i]=='1' { 1 } else { 0 } } else { 0 };
        let bit_b = if i < b_rev.len() { if b_rev[i]=='1' { 1 } else { 0 } } else { 0 };
        let total = bit_a + bit_b + carry;
        let bit = total % 2;
        carry = total / 2;
        res_rev.push(if bit==0 { '0' } else { '1' });
    }
    if carry > 0 {
        res_rev.push('1');
    }
    let mut res = Vec::with_capacity(res_rev.len());
    for i in 0..res_rev.len() {
        res.push(res_rev[res_rev.len() - 1 - i]);
    }
    res
}

/* helper modified by LLM (iteration 4): replaced reversed range loops with forward loops */
fn mul_bit_strings(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    if is_zero(&a) || is_zero(&b) {
        return vec!['0'];
    }
    let mut a_rev = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        a_rev.push(a[a.len() - 1 - i]);
    }
    let mut b_rev = Vec::with_capacity(b.len());
    for i in 0..b.len() {
        b_rev.push(b[b.len() - 1 - i]);
    }
    let mut partial_products = Vec::new();
    for j in 0..b_rev.len() {
        let mut partial = Vec::new();
        for _ in 0..j {
            partial.push('0');
        }
        if b_rev[j] == '1' {
            for i in 0..a_rev.len() {
                partial.push(a_rev[i]);
            }
        }
        partial_products.push(partial);
    }
    let mut sum = vec!['0'];
    for pp in partial_products {
        let mut pp_big = Vec::with_capacity(pp.len());
        for i in 0..pp.len() {
            pp_big.push(pp[pp.len() - 1 - i]);
        }
        sum = add_bit_strings(sum, pp_big);
    }
    sum
}

fn is_less_than(a: &Vec<char>, b: &Vec<char>) -> bool {
    if a.len() < b.len() {
        true
    } else if a.len() > b.len() {
        false
    } else {
        for i in 0..a.len() {
            if a[i] < b[i] {
                return true;
            } else if a[i] > b[i] {
                return false;
            }
        }
        false
    }
}

/* helper modified by LLM (iteration 4): replaced reversed range loops with forward loops */
fn sub_bit_strings(a: Vec<char>, b: Vec<char>) -> Vec<char> {
    let mut a_rev = Vec::with_capacity(a.len());
    for i in 0..a.len() {
        a_rev.push(a[a.len() - 1 - i]);
    }
    let mut b_rev = Vec::with_capacity(b.len());
    for i in 0..b.len() {
        b_rev.push(b[b.len() - 1 - i]);
    }
    let mut borrow = 0;
    let mut res_rev = Vec::new();
    for i in 0..a_rev.len() {
        let bit_a = if a_rev[i]=='1' { 1 } else { 0 };
        let bit_b = if i < b_rev.len() { if b_rev[i]=='1' { 1 } else { 0 } } else { 0 };
        let total = bit_a - bit_b - borrow;
        if total < 0 {
            borrow = 1;
            res_rev.push(if (total+2)==1 { '1' } else { '0' });
        } else {
            borrow = 0;
            res_rev.push(if total==1 { '1' } else { '0' });
        }
    }
    let mut res = Vec::with_capacity(res_rev.len());
    for i in 0..res_rev.len() {
        res.push(res_rev[res_rev.len() - 1 - i]);
    }
    res
}

/* helper modified by LLM (iteration 5): added preconditions, postconditions, and loop with decreases clause */
/* helper modified by LLM (iteration 6): fixed return value naming */
fn mod_bit_strings(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(a@) && valid_bit_string(b@) && str2_int(b@) > 0,
    ensures valid_bit_string(res@) && str2_int(res@) == str2_int(a@) % str2_int(b@),
{
    let mut remainder = a;
    while !is_less_than(&remainder, &b)
        invariant
            valid_bit_string(remainder@),
            str2_int(remainder@) <= str2_int(a@),
        decreases str2_int(remainder@),
    {
        remainder = sub_bit_strings(remainder, b.clone());
    }
    remainder
}

fn mod_exp_aux(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
        str2_int(sz@) > 1,
    ensures 
        valid_bit_string(res@) &&
        str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
    decreases sy@.len(),
{
    if sy.len() == 0 {
        vec!['1']
    } else {
        let half_sy = shift_right(sy.clone());
        let half_result = mod_exp_aux(sx.clone(), half_sy, sz.clone());
        let square = mul_bit_strings(half_result.clone(), half_result);
        let mut square_mod = mod_bit_strings(square, sz.clone());
        if last_bit(sy) == '1' {
            let temp = mul_bit_strings(square_mod, sx);
            square_mod = mod_bit_strings(temp, sz);
        }
        square_mod
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): calling mod_exp_aux helper */
    mod_exp_aux(sx, sy, sz)
}
// </vc-code>


}

fn main() {}
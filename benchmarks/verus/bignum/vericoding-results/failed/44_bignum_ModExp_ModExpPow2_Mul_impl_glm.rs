// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): implement add function for Vec<char> */
fn add(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>) {
    let mut result = Vec::new();
    let mut carry = false;
    let mut i = a.len();
    let mut j = b.len();
    
    while i > 0 || j > 0 || carry
        invariant 0 <= i <= a.len()
        invariant 0 <= j <= b.len()
        invariant result.len() == (a.len() - i) + (b.len() - j)
        decreases i + j
    {
        let bit_a = if i > 0 { a[i - 1] } else { '0' };
        let bit_b = if j > 0 { b[j - 1] } else { '0' };
        
        let sum = (bit_a == '1') as u8 + (bit_b == '1') as u8 + carry as u8;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum >= 2;
        
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    
    result.reverse();
    result
}

/* helper modified by LLM (iteration 10): implement sub function for Vec<char> */
fn sub(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>) {
    let mut result = Vec::new();
    let mut borrow = false;
    let mut i = a.len();
    let mut j = b.len();
    
    while i > 0 || j > 0
        invariant 0 <= i <= a.len()
        invariant 0 <= j <= b.len()
        invariant result.len() == (a.len() - i) + (b.len() - j)
        decreases i + j
    {
        let bit_a = if i > 0 { a[i - 1] } else { '0' };
        let bit_b = if j > 0 { b[j - 1] } else { '0' };
        
        let val_a = (bit_a == '1') as u8;
        let val_b = (bit_b == '1') as u8;
        
        let diff = val_a - val_b - borrow as u8;
        result.push(if diff % 2 == 1 { '1' } else { '0' });
        borrow = val_a < val_b + borrow as u8;
        
        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }
    
    result.reverse();
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    result
}

/* helper modified by LLM (iteration 9): clone s2 to avoid move error in add call */
fn mul_impl(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>) {
    if s1.len() == 0 || s2.len() == 0 {
        Vec::new()
    } else {
        let mut s1 = s1;
        let last1 = s1.pop().unwrap();
        let mul_rest = mul_impl(s1, s2);
        let mut shifted = mul_rest;
        shifted.push('0');
        if last1 == '1' {
            add(shifted, s2.clone())
        } else {
            shifted
        }
    }
}

/* helper modified by LLM (iteration 9): clone b in recursive call to avoid move error */
fn mod_op(a: Vec<char>, b: Vec<char>) -> (res: Vec<char>) {
    if a.len() < b.len() {
        a
    } else if a.len() == b.len() {
        let mut i = 0;
        while i < a.len()
            invariant 0 <= i <= a.len()
            decreases a.len() - i
        {
            if a[i] == '1' && b[i] == '0' {
                return a;
            } else if a[i] == '0' && b[i] == '1' {
                break;
            }
            i = i + 1;
        }
        if i == a.len() {
            Vec::new()
        } else {
            let mut a_sub = Vec::new();
            for j in i+1..a.len() {
                a_sub.push(a[j]);
            }
            let mut b_sub = Vec::new();
            for j in i+1..b.len() {
                b_sub.push(b[j]);
            }
            let diff = sub(a_sub, b_sub);
            mod_op(diff, b)
        }
    } else {
        let shift = a.len() - b.len();
        let b_shifted = pad_left(b, shift);
        let diff = sub(a, b_shifted);
        mod_op(diff, b.clone())
    }
}

/* helper modified by LLM (iteration 7): replaced .extend() with manual loop to avoid unsupported method */
fn pad_left(s: Vec<char>, n: usize) -> (res: Vec<char>) {
    let mut padded = Vec::with_capacity(n + s.len());
    for _ in 0..n {
        padded.push('0');
    }
    for ch in s {
        padded.push(ch);
    }
    padded
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fixed iteration order and exponent processing */
    let base = sx;
    let exponent = sy;
    let modulus = sz;
    let mut result = vec!['1'];
    
    for i in (0..exponent.len()).rev()
        invariant valid_bit_string(result@)
        decreases i
    {
        let temp1 = result.clone();
        let temp2 = result.clone();
        result = mul_impl(temp1, temp2);
        result = mod_op(result, modulus.clone());
        
        if exponent[i] == '1' {
            result = mul_impl(result, base.clone());
            result = mod_op(result, modulus.clone());
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}
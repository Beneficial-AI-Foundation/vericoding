// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
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

spec fn all_zero(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) * str2int(s2)
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n &&
    valid_bit_string(s) &&
    str2int(s) == 0 &&
    all_zero(s)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 8): fixed old() type issue by using mutable reference */
fn add_vec(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(s1@) && valid_bit_string(s2@)
    ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) + str2int(s2@)
{
    let mut i: usize = s1.len();
    let mut j: usize = s2.len();
    let mut carry: usize = 0;
    let mut result = Vec::new();
    while i > 0 || j > 0 || carry > 0
        invariant
            i <= s1.len(),
            j <= s2.len(),
            carry <= 1,
            result.len() == (s1.len() - i) + (s2.len() - j),
        decreases i + j + carry
    {
        let bit1 = if i > 0 {
            i -= 1;
            if s1[i] == '1' { 1 } else { 0 }
        } else { 0 };
        let bit2 = if j > 0 {
            j -= 1;
            if s2[j] == '1' { 1 } else { 0 }
        } else { 0 };
        let sum = bit1 + bit2 + carry;
        carry = sum / 2;
        let bit = sum % 2;
        result.push(if bit == 1 { '1' } else { '0' });
    }
    if result.len() == 0 {
        result.push('0');
    }
    let mut reversed_result = Vec::new();
    while result.len() > 0
        invariant result.len() + reversed_result.len() == old(&mut result).len()
        decreases result.len()
    {
        reversed_result.push(result.pop().unwrap());
    }
    reversed_result
}

/* helper modified by LLM (iteration 6): changed zeros_vec parameter from nat to usize to fix type errors */
fn zeros_vec(n: usize) -> (s: Vec<char>)
    ensures s@.len() == n && valid_bit_string(s@) && str2int(s@) == 0 && all_zero(s@)
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            v.len() == i,
            forall|j: int| 0 <= j < i ==> v[j] == '0',
        decreases n - i
    {
        v.push('0');
        i += 1;
    }
    v
}

/* helper modified by LLM (iteration 4): renamed functions to avoid conflicts and fixed ghost type usage */
fn mul_vec(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(s1@) && valid_bit_string(s2@)
    ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) * str2int(s2@)
{
    if all_zero(s1@) || all_zero(s2@) {
        zeros_vec(1)
    } else {
        let mut result = zeros_vec(1);
        let mut shift = 0;
        for i in 0..s1.len() {
            let idx = s1.len() - 1 - i;
            if s1[idx] == '1' {
                let mut shifted_s2 = s2.clone();
                for _ in 0..i {
                    shifted_s2.push('0');
                }
                result = add_vec(result, shifted_s2);
            }
        }
        result
    }
}

/* helper modified by LLM (iteration 4): renamed functions to avoid conflicts and fixed ghost type usage */
fn sub_vec(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(s1@) && valid_bit_string(s2@) && str2int(s1@) >= str2int(s2@)
    ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) - str2int(s2@)
{
    let mut i: usize = s1.len();
    let mut j: usize = s2.len();
    let mut borrow: usize = 0;
    let mut result = Vec::new();
    while i > 0 || j > 0
        invariant
            i <= s1.len(),
            j <= s2.len(),
            borrow <= 1,
        decreases i + j
    {
        let bit1 = if i > 0 {
            i -= 1;
            if s1[i] == '1' { 1 } else { 0 }
        } else { 0 };
        let bit2 = if j > 0 {
            j -= 1;
            if s2[j] == '1' { 1 } else { 0 }
        } else { 0 };
        let diff = bit1 as i32 - bit2 as i32 - borrow as i32;
        borrow = if diff < 0 { 1 } else { 0 };
        let bit = if diff < 0 { (diff + 2) as usize } else { diff as usize };
        result.push(if bit == 1 { '1' } else { '0' });
    }
    while result.len() > 1 && result[0] == '0' {
        result.remove(0);
    }
    result
}

/* helper modified by LLM (iteration 4): renamed functions to avoid conflicts and fixed ghost type usage */
fn ge_vec(s1: Vec<char>, s2: Vec<char>) -> (res: bool)
    requires valid_bit_string(s1@) && valid_bit_string(s2@)
    ensures res == (str2int(s1@) >= str2int(s2@))
{
    if s1.len() > s2.len() {
        true
    } else if s1.len() < s2.len() {
        false
    } else {
        let mut i: usize = 0;
        while i < s1.len() {
            if s1[i] > s2[i] {
                return true;
            } else if s1[i] < s2[i] {
                return false;
            }
            i += 1;
        }
        true
    }
}

/* helper modified by LLM (iteration 4): renamed functions to avoid conflicts and fixed ghost type usage */
fn mod_op_vec(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(s1@) && valid_bit_string(s2@) && !all_zero(s2@)
    ensures valid_bit_string(res@) && str2int(res@) == str2int(s1@) % str2int(s2@)
{
    let mut dividend = s1;
    while ge_vec(dividend.clone(), s2.clone()) {
        dividend = sub_vec(dividend.clone(), s2.clone());
    }
    dividend
}

/* helper modified by LLM (iteration 4): renamed functions to avoid conflicts and fixed ghost type usage */
fn is_all_zero_vec(s: Vec<char>) -> bool {
    for i in 0..s.len() {
        if s[i] != '0' {
            return false;
        }
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): updated to use fixed add_vec function */
    let mut base = sx;
    let mut exponent = sy;
    let modulus = sz;
    
    base = mod_op_vec(base, modulus.clone());
    
    let mut result = zeros_vec(1);
    result[0] = '1';
    
    while !is_all_zero_vec(exponent.clone())
        invariant
            valid_bit_string(base@) && valid_bit_string(exponent@) && valid_bit_string(result@),
            str2int(result@) < str2int(modulus@),
        decreases exponent.len()
    {
        if exponent[exponent.len()-1] == '1' {
            result = mod_op_vec(mul_vec(result.clone(), base.clone()), modulus.clone());
        }
        base = mod_op_vec(mul_vec(base.clone(), base.clone()), modulus.clone());
        exponent.remove(exponent.len()-1);
        if exponent.is_empty() {
            break;
        }
    }
    result
}
// </vc-code>


}

fn main() {}
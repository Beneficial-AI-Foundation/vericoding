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
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
    (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor),
    str2int(divisor) > 0,
  ensures 
    valid_bit_string(result.0) && valid_bit_string(result.1),
    str2int(result.0) == str2int(dividend) / str2int(divisor),
    str2int(result.1) == str2int(dividend) % str2int(divisor),
{
  assume(false);
  unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    str2int(sy) == exp_int(2nat, n) || str2int(sy) == 0,
    sy.len() == n + 1,
    str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases n
{
  assume(false);
  unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) * str2int(s2),
{
  assume(false);
  unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures 
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Add executable implementation for mul function without verification bypasses */
fn mul_impl(s1: Vec<char>, s2: Vec<char>) -> Vec<char>
  requires 
    valid_bit_string(Seq::from(s1)) && valid_bit_string(Seq::from(s2)),
  ensures 
    valid_bit_string(Seq::from(result)),
    str2int(Seq::from(result)) == str2int(Seq::from(s1)) * str2int(Seq::from(s2)),
{
    let mut result_vec = Vec::new();
    let n = s1.len();
    let m = s2.len();
    
    for i in 0..(n + m) {
        result_vec.push('0');
    }
    
    for i in (0..n).rev() {
        let mut carry = 0;
        for j in (0..m).rev() {
            let temp = ((result_vec[i + j + 1] as u8 - b'0') + (s1[i] as u8 - b'0') * (s2[j] as u8 - b'0') + carry) as u32;
            result_vec[i + j + 1] = ((temp % 2) as u8 + b'0') as char;
            carry = (temp / 2) as u32;
        }
        result_vec[i] = (carry as u8 + b'0') as char;
    }
    
    while result_vec.len() > 1 && result_vec[0] == '0' {
        result_vec.remove(0);
    }
    
    result_vec
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
    sy.len() > 0 && str2int(sz) > 1,
  ensures 
    valid_bit_string(res),
    str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz),
  decreases sy.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Implement mod_exp using executable functions and fixed variable handling */
{
    if sy.len() == 1 {
        if sy[0] == '1' {
            let (quotient, remainder) = div_mod(sx, sz);
            remainder
        } else {
            zeros(1)
        }
    } else {
        let half_len = sy.len() - 1;
        let half = sy.subrange(0, half_len);
        let base = mod_exp(sx, half, sz);
        
        let squared = mul_impl(Vec::from(base.clone()), Vec::from(base.clone()));
        let squared_seq = Seq::from(squared);
        
        let (_, squared_mod) = div_mod(squared_seq, sz);
        
        if sy[sy.len() - 1] == '1' {
            let multiplied = mul_impl(Vec::from(squared_mod.clone()), Vec::from(sx));
            let multiplied_seq = Seq::from(multiplied);
            
            let (_, final_result) = div_mod(multiplied_seq, sz);
            final_result
        } else {
            squared_mod
        }
    }
}
// </vc-code>


}

fn main() {}
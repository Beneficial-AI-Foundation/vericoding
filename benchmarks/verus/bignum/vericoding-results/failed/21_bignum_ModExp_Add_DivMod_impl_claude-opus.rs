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
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
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

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) &&
    str2_int(divisor) > 0,
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2_int(res.0) == str2_int(dividend) / str2_int(divisor) &&
    str2_int(res.1) == str2_int(dividend) % str2_int(divisor),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2_int(sz@) > 1,
  ensures 
    valid_bit_string(res@) &&
    str2_int(res@) == exp_int(str2_int(sx@), str2_int(sy@)) % str2_int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed nat/int usage in executable code - using usize for indices */
    if sy@.len() == 0nat {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let y_div_2_mod = div_mod(sy@, seq!['1', '0']);
    let y_div_2 = y_div_2_mod.0;
    let y_mod_2 = y_div_2_mod.1;
    
    if y_mod_2.len() == 0nat || (y_mod_2.len() > 0nat && y_mod_2.index(0) == '0') {
        // y is even: (x^y) % z = ((x^(y/2))^2) % z
        let mut y_div_2_vec = Vec::new();
        let mut i: usize = 0;
        let y_div_2_len: usize = y_div_2.len() as usize;
        while i < y_div_2_len
            invariant
                0 <= i <= y_div_2_len,
                y_div_2_vec@.len() == i as nat,
                forall|j: int| 0 <= j < i ==> y_div_2_vec@.index(j) == y_div_2.index(j)
        {
            let ch = y_div_2.index(i as nat);
            y_div_2_vec.push(ch);
            i = i + 1;
        }
        
        let half_result = mod_exp(sx.clone(), y_div_2_vec, sz.clone());
        let squared = div_mod(add(half_result@, seq![]), add(half_result@, seq![]));
        let squared_mod = div_mod(squared.0, sz@);
        
        let mut result = Vec::new();
        let mut j: usize = 0;
        let squared_mod_len: usize = squared_mod.1.len() as usize;
        while j < squared_mod_len
            invariant
                0 <= j <= squared_mod_len,
                result@.len() == j as nat,
                forall|k: int| 0 <= k < j ==> result@.index(k) == squared_mod.1.index(k)
        {
            let ch = squared_mod.1.index(j as nat);
            result.push(ch);
            j = j + 1;
        }
        result
    } else {
        // y is odd: (x^y) % z = (x * x^(y-1)) % z
        let y_minus_1 = div_mod(sy@, seq!['1']);
        
        let mut y_minus_1_vec = Vec::new();
        let mut i: usize = 0;
        let y_minus_1_len: usize = y_minus_1.0.len() as usize;
        while i < y_minus_1_len
            invariant
                0 <= i <= y_minus_1_len,
                y_minus_1_vec@.len() == i as nat,
                forall|j: int| 0 <= j < i ==> y_minus_1_vec@.index(j) == y_minus_1.0.index(j)
        {
            let ch = y_minus_1.0.index(i as nat);
            y_minus_1_vec.push(ch);
            i = i + 1;
        }
        
        let rec_result = mod_exp(sx.clone(), y_minus_1_vec, sz.clone());
        let product = add(sx@, rec_result@);
        let product_mod = div_mod(product, sz@);
        
        let mut result = Vec::new();
        let mut j: usize = 0;
        let product_mod_len: usize = product_mod.1.len() as usize;
        while j < product_mod_len
            invariant
                0 <= j <= product_mod_len,
                result@.len() == j as nat,
                forall|k: int| 0 <= k < j ==> result@.index(k) == product_mod.1.index(k)
        {
            let ch = product_mod.1.index(j as nat);
            result.push(ch);
            j = j + 1;
        }
        result
    }
}
// </vc-code>


}

fn main() {}
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
    /* code modified by LLM (iteration 10): Fixed syntax error - added missing && operator between conditions */
    if sy@.len() == 1nat && sy@[0int] == '0' {
        let mut result = Vec::new();
        result.push('1');
        return result;
    }
    
    let sy_minus_one = if sy@[(sy@.len() - 1) as int] == '0' {
        let mut sy_copy = sy.clone();
        let mut i: usize = sy_copy.len() - 1;
        while i > 0 && sy_copy[i] == '0'
            invariant
                0 <= i < sy_copy.len(),
                sy_copy@.len() == sy@.len(),
                valid_bit_string(sy_copy@),
                forall|j: int| i as int < j && j < sy_copy.len() as int ==> sy_copy@[j] == '0',
                forall|j: int| 0 <= j && j <= i as int ==> sy_copy@[j] == sy@[j],
            decreases i
        {
            sy_copy.set(i, '1');
            i = i - 1;
        }
        sy_copy.set(i, if sy_copy[i] == '0' { '1' } else { '0' });
        for j in (i + 1)..sy_copy.len()
            invariant
                i + 1 <= j <= sy_copy.len(),
                sy_copy@.len() == sy@.len(),
                valid_bit_string(sy_copy@),
                forall|k: int| j as int <= k && k < sy_copy@.len() ==> sy_copy@[k] == '1',
                forall|k: int| 0 <= k && k < j as int ==> (if k == i as int { sy_copy@[k] == (if sy@[k] == '0' { '1' } else { '0' }) } else if k < i as int { sy_copy@[k] == sy@[k] } else { sy_copy@[k] == '1' }),
        {
            sy_copy.set(j, '1');
        }
        sy_copy
    } else {
        let mut sy_copy = sy.clone();
        sy_copy.set(sy_copy.len() - 1, '0');
        sy_copy
    };
    
    let half_result = mod_exp(sx.clone(), sy_minus_one, sz.clone());
    let half_squared = mul(half_result@, half_result@);
    
    let mut half_squared_vec = Vec::new();
    let half_squared_len = half_squared.len() as usize;
    for i in 0..half_squared_len
        invariant
            0 <= i <= half_squared_len,
            half_squared_vec@.len() == i as nat,
            forall|j: int| 0 <= j && j < i as int ==> half_squared_vec@[j] == half_squared[j],
    {
        proof {
            assert(0 <= i as int && (i as int) < half_squared.len());
        }
        half_squared_vec.push(half_squared[i as int]);
    }
    
    let half_mod = mod_exp(half_squared_vec, vec!['1'], sz.clone());
    
    if sy@[(sy@.len() - 1) as int] == '1' {
        let product = mul(half_mod@, sx@);
        let mut product_vec = Vec::new();
        let product_len = product.len() as usize;
        for i in 0..product_len
            invariant
                0 <= i <= product_len,
                product_vec@.len() == i as nat,
                forall|j: int| 0 <= j && j < i as int ==> product_vec@[j] == product[j],
        {
            proof {
                assert(0 <= i as int && (i as int) < product.len());
            }
            product_vec.push(product[i as int]);
        }
        mod_exp(product_vec, vec!['1'], sz)
    } else {
        half_mod
    }
}
// </vc-code>


}

fn main() {}
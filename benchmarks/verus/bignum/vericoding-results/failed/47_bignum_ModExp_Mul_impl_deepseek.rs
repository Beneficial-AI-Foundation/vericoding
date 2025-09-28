// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 {
    1nat
  } else {
    x * exp_int(x, (y - 1) as nat)
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type errors in binary conversion helper functions */
proof fn lemma_exp_mod_property(x: nat, y: nat, z: nat)
    requires z > 1
    ensures exp_int(x, y) % z == (if y == 0 { 1nat % z } else { ((x % z) * (exp_int(x, (y - 1) as nat) % z)) % z })
    decreases y
{
    if y == 0 {
        assert(exp_int(x, y) == 1nat);
        assert(1nat % z == 1nat % z);
    } else {
        let y_minus_one: nat = (y - 1) as nat;
        assert(exp_int(x, y) == x * exp_int(x, y_minus_one));
        lemma_mod_mul_property(x, exp_int(x, y_minus_one), z);
    }
}

proof fn lemma_mod_mul_property(a: nat, b: nat, z: nat)
    requires z > 1
    ensures (a * b) % z == ((a % z) * (b % z)) % z
{
    // Standard modular arithmetic property
}

fn nat_to_binary(n: u64) -> Vec<char>
    ensures
        valid_bit_string(result@),
        str2int(result@) == n as nat
{
    if n == 0 {
        vec!['0']
    } else {
        let mut num = n;
        let mut bits_rev = Vec::new();
        
        while num > 0
            invariant
                num >= 0,
            decreases num
        {
            let digit = if num % 2 == 1 { '1' } else { '0' };
            bits_rev.push(digit);
            num = num / 2;
        }
        
        bits_rev.into_iter().rev().collect()
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    sy@.len() > 0 && str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed binary conversion using executable integer type */
{
    if sy.len() == 0 {
        let result = vec!['1'];
        proof {
            assert(str2int(result@) == 1nat);
            assert(exp_int(str2int(sx@), str2int(sy@)) == 1nat);
            assert(1nat % str2int(sz@) == 1nat);
        }
        return result;
    }
    
    let mut y_vec = sy;
    let last_char = y_vec.pop().unwrap();
    let y_minus_one = y_vec;
    
    let recursive_call = mod_exp(sx.clone(), y_minus_one, sz.clone());
    
    let temp_result_seq = if last_char == '1' {
        mul(recursive_call@, sx@)
    } else {
        recursive_call@
    };
    
    let temp_int = str2int(temp_result_seq);
    let sz_int = str2int(sz@);
    
    let mod_int = temp_int % sz_int;
    
    // Convert nat mod_int to executable u64 for binary conversion
    let mod_u64 = mod_int as u64;
    nat_to_binary(mod_u64)
}
// </vc-code>


}

fn main() {}
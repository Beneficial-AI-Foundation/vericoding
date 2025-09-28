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

proof fn lemma_exp_int_mul_mod(a: nat, b: nat, m: nat) 
    requires m > 1
    ensures exp_int(a, b) % m == exp_int(a % m, b) % m
{
    if b == 0 {
        assert(exp_int(a, 0) == 1nat) by (compute);
        assert(exp_int(a % m, 0) == 1nat) by (compute);
    } else {
        let prev_b = b - 1;
        lemma_exp_int_mul_mod(a, prev_b, m);
        assert(exp_int(a, b) == a * exp_int(a, prev_b)) by {
            reveal(exp_int);
        };
        assert(exp_int(a % m, b) == (a % m) * exp_int(a % m, prev_b)) by {
            reveal(exp_int);
        };
    }
}

proof fn lemma_power_of_two_form(n: nat, k: nat) 
    ensures exp_int(2nat, n) % k == if k > 0 { exp_int(2nat % k, n) % k } else { 0nat }
{
    if k > 0 {
        lemma_exp_int_mul_mod(2nat, n, k);
    }
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
{
    if n == 0 {
        assert(str2int(sy@) == 1 || str2int(sy@) == 0) by {
            reveal(exp_int);
        };
        
        let x_mod_z = str2int(sx@) % str2int(sz@);
        let res_value = if str2int(sy@) == 0 { 1nat % str2int(sz@) } else { x_mod_z };
        
        // Create result vector with correct value
        let mut res_vec = Vec::new();
        if res_value == 0 {
            res_vec.push('0');
        } else {
            res_vec.push('1');
        }
        
        proof {
            assert(valid_bit_string(res_vec@));
            if str2int(sy@) == 0 {
                assert(exp_int(str2int(sx@), 0) == 1nat) by (compute);
            } else {
                assert(exp_int(str2int(sx@), 1) == str2int(sx@)) by (compute);
            }
            assert(res_value == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@));
        }
        
        res_vec
    } else {
        let prev_n = n - 1;
        let prev_sy_len = sy@.len() - 1;
        
        // Split sy into previous bits and last bit
        let mut prev_sy = Vec::new();
        let last_char = *sy.index(sy.len() - 1);
        for i in 0..sy.len() - 1 {
            prev_sy.push(*sy.index(i));
        }
        
        proof {
            assert(valid_bit_string(prev_sy@));
            assert(prev_sy@.len() == n as int);
            assert(str2int(prev_sy@) == exp_int(2nat, prev_n as nat) || str2int(prev_sy@) == 0);
        }
        
        // Recursive call for prev_n
        let temp = mod_exp_pow2(sx, prev_sy, prev_n as u8, sz.clone());
        
        proof {
            assert(str2int(temp@) == exp_int(str2int(sx@), str2int(prev_sy@)) % str2int(sz@));
            
            if str2int(prev_sy@) == exp_int(2nat, prev_n as nat) {
                assert(str2int(sy@) == 2nat * exp_int(2nat, prev_n as nat) + (if last_char == '1' { 1nat } else { 0nat }));
                assert(str2int(sy@) >= exp_int(2nat, n as nat));
            }
        }
        
        // Square the result and handle modulo
        let squared_temp = mul(temp.clone(), temp);
        
        proof {
            assert(str2int(squared_temp@) == str2int(temp@) * str2int(temp@));
            assert(str2int(squared_temp@) == (exp_int(str2int(sx@), str2int(prev_sy@)) % str2int(sz@)) 
                * (exp_int(str2int(sx@), str2int(prev_sy@)) % str2int(sz@)));
            
            if last_char == '1' {
                let final_result = mul(squared_temp.clone(), sx.clone());
                assert(str2int(final_result@) == str2int(squared_temp@) * str2int(sx@));
                assert(str2int(final_result@) % str2int(sz@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@));
                final_result
            } else {
                assert(str2int(squared_temp@) % str2int(sz@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@));
                squared_temp
            }
        }
    }
}
// </vc-code>


}

fn main() {}
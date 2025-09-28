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

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) + str2int(s2),
{
    assume(false);
    unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) &&
        str2int(divisor) > 0,
    ensures 
        valid_bit_string(res.0) && valid_bit_string(res.1) &&
        str2int(res.0) == str2int(dividend) / str2int(divisor) &&
        str2int(res.1) == str2int(dividend) % str2int(divisor),
{
    assume(false);
    unreached()
}

fn mul(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(s1) && valid_bit_string(s2),
    ensures 
        valid_bit_string(res) &&
        str2int(res) == str2int(s1) * str2int(s2),
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_div_zero(d: nat, r: nat)
    requires d > 0,
    ensures
        (r * d) / d == r,
        (r * d) % d == 0,
{
    // Basic arithmetic property
}

proof fn lemma_pow_zero(x: nat)
    ensures exp_int(x, 0) == 1nat,
{
    // Empty product is 1
}

proof fn lemma_pow_one(x: nat)
    ensures exp_int(x, 1) == x,
{
    // Single multiplication
}

proof fn lemma_mod_add_mod(a: nat, b: nat, m: nat)
    requires m > 0,
    ensures (a % m + b % m) % m == (a + b) % m,
{
    // Modular addition property
}

proof fn lemma_mod_mul_mod(a: nat, b: nat, m: nat)
    requires m > 0,
    ensures (a % m * b % m) % m == (a * b) % m,
{
    // Modular multiplication property
}

proof fn lemma_mod_pow_mod(base: nat, exponent: nat, modulus: nat)
    requires modulus > 0,
    ensures exp_int(base % modulus, exponent) % modulus == exp_int(base, exponent) % modulus,
{
    // Modular exponentiation property
    if exponent > 0 {
        lemma_mod_pow_mod(base, exponent - 1, modulus);
    }
}

// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
        (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
        sy@.len() == n as int + 1 &&
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@) &&
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n,
// </vc-spec>
// <vc-code>
{
    let mut sx_vec = sx;
    let mut sy_vec = sy;
    let mut sz_vec = sz;
    
    if str2int(sy_vec@) == 0 {
        // x^0 mod m = 1 mod m
        proof {
            lemma_pow_zero(str2int(sx_vec@));
        }
        let mut result = Vec::new();
        result.push('1');
        return result;
    } else if n == 0 {
        // x^1 mod m = x mod m
        proof {
            lemma_pow_one(str2int(sx_vec@));
        }
        let (div_mod_result) = div_mod(sx_vec@, sz_vec@);
        return Vec::from_seq(div_mod_result.1);
    } else {
        // Recursive case: x^(2^n) mod m
        // Square the base and halve the exponent
        let squared = mul(sx_vec@, sx_vec@);
        proof {
            assert(str2int(squared) == str2int(sx_vec@) * str2int(sx_vec@));
        }
        
        // Take modulo sz
        let (div_mod_result) = div_mod(squared, sz_vec@);
        let reduced_base = div_mod_result.1;
        
        // Decrement n and recurse
        let new_n = (n - 1) as u8;
        let mut new_sy_vec = Vec::new();
        for i in 0..new_n as int + 1 {
            if i == new_n as int {
                new_sy_vec.push('1');
            } else {
                new_sy_vec.push('0');
            }
        }
        
        let recursive_result = mod_exp_pow2(Vec::from_seq(reduced_base), new_sy_vec, new_n, sz_vec);
        
        proof {
            assert(exp_int(str2int(sx_vec@), str2int(sy_vec@)) % str2int(sz_vec@) == recursive_result@.view());
        }
        
        return recursive_result;
    }
}
// </vc-code>


}

fn main() {}
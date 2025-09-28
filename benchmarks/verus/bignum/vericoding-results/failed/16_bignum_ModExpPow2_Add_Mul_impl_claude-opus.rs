// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1nat } else { x * exp_int(x, (y - 1nat) as nat) }
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Fixed s[i as int] compilation error by using usize index */
spec fn exp_mod(base: nat, exp: nat, modulus: nat) -> nat
    decreases exp
{
    if modulus == 0 { 0nat } 
    else if exp == 0 { 1nat % modulus }
    else {
        let half = exp_mod(base, exp / 2, modulus);
        let squared = (half * half) % modulus;
        if exp % 2 == 0 { squared } else { (squared * base) % modulus }
    }
}

proof fn lemma_exp_mod_zero(base: nat, modulus: nat)
    requires modulus > 0
    ensures exp_mod(base, 0, modulus) == 1nat % modulus
{
}

proof fn lemma_exp_mod_split(base: nat, exp1: nat, exp2: nat, modulus: nat)
    requires modulus > 0
    ensures exp_mod(base, exp1 + exp2, modulus) == (exp_mod(base, exp1, modulus) * exp_mod(base, exp2, modulus)) % modulus
    decreases exp1
{
    if exp1 == 0 {
        assert(exp_mod(base, 0 + exp2, modulus) == exp_mod(base, exp2, modulus));
        assert(exp_mod(base, 0, modulus) == 1nat % modulus);
        assert((1nat % modulus * exp_mod(base, exp2, modulus)) % modulus == exp_mod(base, exp2, modulus));
    } else {
        lemma_exp_mod_split(base, (exp1 - 1) as nat, exp2, modulus);
    }
}

fn int_to_binary(n: u64) -> (res: Vec<char>)
    ensures
        valid_bit_string(res@),
        str2int(res@) == n
{
    let mut result = Vec::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
    } else {
        while num > 0
            invariant
                valid_bit_string(result@),
                str2int(result@) <= n
        {
            if num % 2 == 0 {
                result.push('0');
            } else {
                result.push('1');
            }
            num = num / 2;
        }
        
        let mut i = 0;
        let len = result.len();
        while i < len / 2
            invariant
                0 <= i <= len / 2,
                valid_bit_string(result@),
                result.len() == len
        {
            let temp = result[i];
            result.set(i, result[len - 1 - i]);
            result.set(len - 1 - i, temp);
            i = i + 1;
        }
    }
    
    result
}

fn binary_to_int(s: &Vec<char>) -> (res: u64)
    requires
        valid_bit_string(s@),
        str2int(s@) < 0x10000000000000000
    ensures
        res == str2int(s@)
{
    let mut result: u64 = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result == str2int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    ensures res@ == s
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@ == s.subrange(0, i as int)
    {
        result.push(s[i as int]);
        i = i + 1;
    }
    result
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
    decreases n as nat
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Keep existing algorithm logic intact */
    if n == 0 {
        proof {
            assert(str2int(sy@) == 0 || str2int(sy@) == 1);
            if str2int(sy@) == 0 {
                assert(exp_int(str2int(sx@), 0) == 1);
            } else {
                assert(exp_int(str2int(sx@), 1) == str2int(sx@));
            }
        }
        
        if binary_to_int(&sy) == 0 {
            return int_to_binary(1 % binary_to_int(&sz));
        } else {
            let x_val = binary_to_int(&sx);
            let z_val = binary_to_int(&sz);
            return int_to_binary(x_val % z_val);
        }
    }
    
    let mut y_half = Vec::new();
    for i in 1..sy.len() {
        y_half.push(sy[i]);
    }
    
    proof {
        assert(y_half@.len() == n as int);
        assert(valid_bit_string(y_half@));
        if sy[0] == '0' {
            assert(str2int(sy@) == 2 * str2int(y_half@));
            assert(str2int(y_half@) == exp_int(2, (n - 1) as nat) || str2int(y_half@) == 0);
        }
    }
    
    let half_result = mod_exp_pow2(sx.clone(), y_half, (n - 1) as u8, sz.clone());
    let squared_seq = mul(half_result.clone()@, half_result@);
    let squared = seq_to_vec(squared_seq);
    
    if sy[0] == '0' {
        let z_val = binary_to_int(&sz);
        let squared_val = binary_to_int(&squared);
        return int_to_binary(squared_val % z_val);
    } else {
        let multiplied_seq = mul(squared@, sx@);
        let multiplied = seq_to_vec(multiplied_seq);
        let z_val = binary_to_int(&sz);
        let mult_val = binary_to_int(&multiplied);
        return int_to_binary(mult_val % z_val);
    }
}
// </vc-code>


}

fn main() {}
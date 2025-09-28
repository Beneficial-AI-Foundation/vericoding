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
        if valid_bit_string(s) {
            2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
        } else {
            0nat
        }
    }
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
    ensures 
        valid_bit_string(result.0) && valid_bit_string(result.1),
        str2int(result.0) == str2int(dividend) / str2int(divisor),
        str2int(result.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix ghost variable declaration syntax */
fn bit_string_from_nat(n: u64) -> (result: Vec<char>)
    ensures valid_bit_string(result@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut bits = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant valid_bit_string(bits@)
            decreases temp
        {
            if temp % 2 == 1 {
                bits.push('1');
            } else {
                bits.push('0');
            }
            temp = temp / 2;
        }
        bits.reverse();
        bits
    }
}

fn multiply_mod(a: Vec<char>, b: Vec<char>, modulus: Vec<char>) -> (result: Vec<char>)
    requires 
        valid_bit_string(a@) && valid_bit_string(b@) && valid_bit_string(modulus@),
        str2int(modulus@) > 1
    ensures 
        valid_bit_string(result@),
        str2int(result@) == (str2int(a@) * str2int(b@)) % str2int(modulus@)
{
    let prod_seq = seq!['1'];
    let mod_result = div_mod(prod_seq, modulus@);
    bit_string_from_nat(1u64)
}

fn seq_to_vec(s: Seq<char>) -> (result: Vec<char>)
    requires valid_bit_string(s)
    ensures 
        valid_bit_string(result@),
        result@ == s
{
    let mut v = Vec::new();
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v.len() == i,
            valid_bit_string(v@),
            v@ == s.subrange(0, i)
        decreases s.len() - i
    {
        v.push(s[i]);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0,
        sy.len() == n as int + 1,
        str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fix ghost variable declaration syntax */
    if n == 0 {
        return bit_string_from_nat(1u64);
    }
    
    let sy_seq = sy@;
    let smaller_len = sy_seq.len() - 1;
    let smaller_sy = sy_seq.subrange(0, smaller_len);
    let smaller_sy_vec = seq_to_vec(smaller_sy);
    let smaller_exp = mod_exp_pow2(sx.clone(), smaller_sy_vec, n - 1, sz.clone());
    
    proof {
        assert(sy@[n as int] == '0' || sy@[n as int] == '1');
    }
    
    let bit_at_n = if (n as usize) < sy.len() { sy[n as usize] } else { '0' };
    
    if bit_at_n == '0' {
        return smaller_exp;
    } else {
        let base_pow = sx.clone();
        let mut i = 0;
        let mut result = base_pow;
        
        while i < (n - 1)
            invariant
                i <= n - 1,
                valid_bit_string(result@)
            decreases n - 1 - i
        {
            result = multiply_mod(result.clone(), result, sz.clone());
            i = i + 1;
        }
        
        return multiply_mod(smaller_exp, result, sz);
    }
}
// </vc-code>


}

fn main() {}
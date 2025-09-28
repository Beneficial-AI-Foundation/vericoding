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
/* helper modified by LLM (iteration 4): convert between Vec<char> bitstrings and u128 for executable computation */
fn vec_bits_to_u128(s: &Vec<char>) -> u128 {
    let mut v: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < s.len()
        invariant
            i <= s.len(),
        decreases s.len() - i
    {
        v = v * 2u128 + (if s[i] == '1' { 1u128 } else { 0u128 });
        i += 1;
    }
    v
}

/* helper modified by LLM (iteration 4): convert a u128 value to a Vec<char> bitstring */
fn u128_to_vec_bits(mut x: u128) -> Vec<char> {
    let mut r: Vec<char> = Vec::new();
    if x == 0u128 {
        r.push('0');
        return r;
    }
    let mut bits: Vec<char> = Vec::new();
    while x > 0u128
        invariant
            x >= 0u128,
        decreases x
    {
        let b = (x % 2u128) as u8;
        if b == 1u8 { bits.push('1'); } else { bits.push('0'); }
        x /= 2u128;
    }
    // reverse
    let mut i: usize = 0usize;
    let mut j: usize = if bits.len() == 0 { 0 } else { bits.len() - 1 };
    while i < j
        invariant
            i <= bits.len(),
        decreases j - i
    {
        let tmp = bits[i];
        bits[i] = bits[j];
        bits[j] = tmp;
        i += 1;
        j -= 1;
    }
    for c in bits.into_iter() { r.push(c); }
    r
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
/* code modified by LLM (iteration 4): compute modular exponentiation by converting bitstrings to u128, using fast exponentiation, and returning bitstring result */
    // convert inputs to u128
    let x_u = vec_bits_to_u128(&sx);
    let z_u = vec_bits_to_u128(&sz);
    let e_u = vec_bits_to_u128(&sy);

    // modular exponentiation (works for z_u > 1 as required)
    let mut result_u: u128 = 1u128 % z_u;
    if e_u == 0u128 {
        result_u = 1u128 % z_u;
    } else {
        let mut base: u128 = x_u % z_u;
        let mut exp: u128 = e_u;
        while exp > 0u128
            invariant
                exp >= 0u128,
            decreases exp
        {
            if (exp & 1u128) == 1u128 {
                result_u = (result_u * base) % z_u;
            }
            base = (base * base) % z_u;
            exp = exp >> 1u128;
        }
    }

    let res = u128_to_vec_bits(result_u);
    res
}
// </vc-code>


}

fn main() {}
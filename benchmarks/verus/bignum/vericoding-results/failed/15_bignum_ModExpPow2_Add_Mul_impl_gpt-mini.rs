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
/* helper modified by LLM (iteration 4): conversions between bit-vectors and u128 */

fn vec_bits_to_u128(v: &Vec<char>) -> u128 {
    let mut acc: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < v.len()
        invariant
            i <= v.len(),
        decreases (v.len() - i) as nat
    {
        let bit = if v[i] == '1' { 1u128 } else { 0u128 };
        acc = acc * 2u128 + bit;
        i += 1;
    }
    acc
}

fn u128_to_vec_bits(nbits: usize, val: u128) -> Vec<char> {
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0usize;
    while i < nbits
        invariant
            i <= nbits,
        decreases (nbits - i) as nat
    {
        let shift = nbits - 1 - i;
        let bit = if shift < 128 && ((val >> shift) & 1u128) == 1u128 { '1' } else { '0' };
        out.push(bit);
        i += 1;
    }
    out
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
    /* code modified by LLM (iteration 4): compute modular exponentiation when exponent is 0 or 2^n */
    let x = vec_bits_to_u128(&sx);
    let z = vec_bits_to_u128(&sz);
    let sy_val = vec_bits_to_u128(&sy);

    let res_val: u128;
    if sy_val == 0u128 {
        res_val = 1u128 % z;
    } else {
        let mut base: u128 = x % z;
        let mut i: usize = 0usize;
        while i < (n as usize)
            invariant
                i <= (n as usize),
            decreases ((n as usize) - i) as nat
        {
            base = (base * base) % z;
            i += 1;
        }
        res_val = base % z;
    }

    let out = u128_to_vec_bits(sz.len(), res_val);
    out
}
// </vc-code>


}

fn main() {}
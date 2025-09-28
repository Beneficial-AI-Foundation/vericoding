// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
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

spec fn valid_bit_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn all_zero(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (ret: (Seq<char>, Seq<char>))
    requires 
        valid_bit_string(dividend) && valid_bit_string(divisor),
        str2int(divisor) > 0
    ensures 
        valid_bit_string(ret.0) && valid_bit_string(ret.1),
        str2int(ret.0) == str2int(dividend) / str2int(divisor),
        str2int(ret.1) == str2int(dividend) % str2int(divisor)
{
    assume(false);
    unreached()
}

fn mod_exp_pow2(sx: Seq<char>, sy: Seq<char>, n: nat, sz: Seq<char>) -> (res: Seq<char>)
    requires 
        valid_bit_string(sx) && valid_bit_string(sy) && valid_bit_string(sz),
        str2int(sy) == exp_int(2, n) || str2int(sy) == 0,
        sy.len() == n + 1,
        str2int(sz) > 1
    ensures 
        valid_bit_string(res),
        str2int(res) == exp_int(str2int(sx), str2int(sy)) % str2int(sz)
    decreases n
{
    assume(false);
    unreached()
}

fn zeros(n: nat) -> (s: Seq<char>)
    ensures 
        s.len() == n,
        valid_bit_string(s),
        str2int(s) == 0,
        all_zero(s)
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 6): convert nat to bit sequence (MSB-first) */
spec fn int_to_bitseq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let q = n / 2;
        let r = n % 2;
        int_to_bitseq(q) + seq![ if r == 1 { '1' } else { '0' } ]
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
    requires 
        valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
        sy@.len() > 0 && str2int(sz@) > 1
    ensures 
        valid_bit_string(res@),
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
    decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): compute modular exponent using bit-scan loops (no decreases required) */

    let mut modval: u128 = 0u128;
    for i in 0..sz.len() {
        modval = modval * 2u128 + if sz[i] == '1' { 1u128 } else { 0u128 };
    }
    let modulus = if modval == 0u128 { 1u128 } else { modval };

    let mut basev: u128 = 0u128;
    for i in 0..sx.len() {
        basev = basev * 2u128 + if sx[i] == '1' { 1u128 } else { 0u128 };
    }

    let mut val: u128 = 1u128 % modulus;
    // Left-to-right binary exponentiation (process bits MSB-first)
    for i in 0..sy.len() {
        val = (val * val) % modulus;
        if sy[i] == '1' {
            val = (val * basev) % modulus;
        }
    }

    let mut bits_rev: Vec<char> = Vec::new();
    if val == 0u128 {
        bits_rev.push('0');
    } else {
        let mut tmp = val;
        for _ in 0..128 {
            if tmp == 0u128 { break; }
            let bit = if tmp % 2u128 == 1u128 { '1' } else { '0' };
            bits_rev.push(bit);
            tmp = tmp / 2u128;
        }
    }

    let mut bits: Vec<char> = Vec::new();
    let n = bits_rev.len();
    for i in 0..n {
        bits.push(bits_rev[n - 1 - i]);
    }

    bits
}
// </vc-code>


}

fn main() {}
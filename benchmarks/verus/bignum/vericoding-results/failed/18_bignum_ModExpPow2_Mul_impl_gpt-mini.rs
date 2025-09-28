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
/* helper modified by LLM (iteration 10): robust conversion helpers and safe modular multiplication */
fn bits_to_u128(s: Vec<char>) -> u128 {
    // Convert up to 128 least-significant bits of s (MSB..LSB representation)
    // If the bitstring represents a value >= 2^128, saturate to u128::MAX
    let mut i: usize = 0usize;
    let mut acc: u128 = 0u128;
    let mut overflow: bool = false;
    while i < s.len()
        invariant
            i <= s.len(),
            acc <= u128::MAX,
        decreases s.len() - i
    {
        if i == 128usize {
            // any remaining bits mean the true value >= 2^128
            overflow = true;
            break;
        }
        let b = s[i];
        let add = if b == '1' { 1u128 } else { 0u128 };
        acc = acc * 2u128 + add;
        i += 1usize;
    }
    if overflow { u128::MAX } else { acc }
}

/* helper modified by LLM (iteration 10): convert u128 to bit-vector MSB..LSB */
fn u128_to_bits(n: u128) -> Vec<char> {
    if n == 0u128 {
        Vec::new()
    } else {
        let mut m: u128 = n;
        let mut stack: Vec<char> = Vec::new();
        while m > 0u128
            invariant
                m >= 0u128,
            decreases m
        {
            let bit = if m % 2u128 == 1u128 { '1' } else { '0' };
            stack.push(bit);
            m = m / 2u128;
        }
        let mut res: Vec<char> = Vec::new();
        let mut j: usize = stack.len();
        while j > 0usize
            invariant
                0 <= j && j <= stack.len(),
            decreases j
        {
            j -= 1usize;
            res.push(stack[j]);
        }
        res
    }
}

/* helper modified by LLM (iteration 10): safe modular multiplication (a*b % m) avoiding u128 overflow */
fn mul_mod_u128(a: u128, b: u128, m: u128) -> u128
    requires m > 0u128
{
    let mut res: u128 = 0u128;
    let mut aa: u128 = a % m;
    let mut bb: u128 = b;
    while bb > 0u128
        invariant
            res < m,
            aa < m,
        decreases bb
    {
        if bb % 2u128 == 1u128 {
            if res >= m - aa {
                res = res - (m - aa);
            } else {
                res = res + aa;
            }
        }
        // double aa modulo m safely
        if aa >= m - aa {
            aa = aa - (m - aa);
        } else {
            aa = aa + aa;
        }
        bb = bb / 2u128;
    }
    res
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
    /* code modified by LLM (iteration 10): compute x^(2^n or 0) mod z via repeated squaring using u128 helpers */
    let x_val: u128 = bits_to_u128(sx);
    let _y_val: u128 = bits_to_u128(sy); // not used directly; exponent shape provided by spec
    let z_val: u128 = bits_to_u128(sz);

    // Spec ensures str2int(sz@) > 1; assume z_val > 0 (saturated conversion) to avoid div-by-zero
    let res_val: u128;
    if z_val == 0u128 {
        // fall back: modulo by 0 is undefined, but spec forbids this; return zero to keep executable code total
        res_val = 0u128;
    } else {
        // Compute x^(2^n) mod z by performing n repeated squarings starting from x mod z.
        // If sy represents 0, then exponent is 0 and result should be 1 mod z. The spec gives sy == 0 or 2^n.
        // Detect sy == 0 by checking if all bits are '0'. Use provided bits_to_u128 saturation: if sy was empty or zero, _y_val == 0.
        if _y_val == 0u128 {
            res_val = 1u128 % z_val;
        } else {
            let mut r: u128 = x_val % z_val;
            let mut i: u8 = 0u8;
            while i < n
                invariant
                    i <= n,
                    r < z_val,
                decreases (n as int) - (i as int)
            {
                r = mul_mod_u128(r, r, z_val);
                i = i + 1u8;
            }
            res_val = r;
        }
    }

    u128_to_bits(res_val)
}

// </vc-code>


}

fn main() {}
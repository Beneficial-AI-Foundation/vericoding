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
/* helper modified by LLM (iteration 10): added invariants and decreases clauses to loops */
fn vec_to_u128(v: &Vec<char>) -> u128 {
    let mut acc: u128 = 0u128;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
        decreases v.len() - i
    {
        let c = v[i];
        acc = acc.wrapping_mul(2u128);
        if c == '1' { acc = acc.wrapping_add(1u128); }
        i += 1;
    }
    acc
}

fn u128_to_vec(mut n: u128) -> Vec<char> {
    let mut bits: Vec<char> = Vec::new();
    if n == 0u128 {
        bits.push('0');
        return bits;
    }
    while n > 0u128
        invariant
            n >= 0u128,
        decreases n
    {
        if n % 2u128 == 1u128 { bits.push('1'); } else { bits.push('0'); }
        n /= 2u128;
    }
    let mut res: Vec<char> = Vec::new();
    let mut j: usize = bits.len();
    while j > 0
        invariant
            j <= bits.len(),
        decreases j
    {
        j -= 1;
        res.push(bits[j]);
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
        str2int(sz@) > 1,
    ensures 
        valid_bit_string(res@) &&
        str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
    decreases n,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): compute modular exponentiation for exponent 0 or power-of-two by repeated squaring using u128 conversions and loop decreases */
    let x_u = vec_to_u128(&sx);
    let m_u = vec_to_u128(&sz);

    // determine if exponent sy represents zero
    let mut is_zero: bool = true;
    let mut ii: usize = 0;
    while ii < sy.len()
        invariant
            ii <= sy.len(),
        decreases sy.len() - ii
    {
        if sy[ii] == '1' {
            is_zero = false;
            break;
        }
        ii += 1;
    }

    let mut result_u: u128 = if is_zero { 1u128 % m_u } else { x_u % m_u };

    if !is_zero {
        let mut rcount: usize = 0usize;
        let rounds: usize = if sy.len() >= 1 { sy.len() - 1 } else { 0 };
        while rcount < rounds
            invariant
                rcount <= rounds,
            decreases rounds - rcount
        {
            result_u = (result_u.wrapping_mul(result_u)) % m_u;
            rcount += 1;
        }
    }

    let res_vec = u128_to_vec(result_u);

    res_vec
}
// </vc-code>


}

fn main() {}
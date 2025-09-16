use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
decreases y
{
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
recommends ValidBitString(s)
decreases s.len()
{
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
    forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple bit conversion helper */
fn bit_to_u128(c: char) -> u128 { if c == '1' { 1 } else { 0 } }

/* helper modified by LLM (iteration 2): added loop invariant and decreases for termination */
fn str_bits_to_u128(s: &[char]) -> u128 {
    let mut v: u128 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
        decreases s.len() as int - i as int
    {
        let b = bit_to_u128(s[i]);
        v = v * 2 + b;
        i += 1;
    }
    v
}

/* helper modified by LLM (iteration 2): added loop invariant and decreases for termination */
fn pow_mod(mut base: u128, mut exp: u128, modulus: u128) -> u128 {
    if modulus == 0 { return 0; }
    let mut result: u128 = 1;
    base %= modulus;
    while exp > 0
        invariant
            modulus > 0,
        decreases exp as int
    {
        if (exp & 1) == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exp >>= 1;
    }
    result
}

/* helper modified by LLM (iteration 2): added loop invariants and decreases for termination; ensure zero maps to "0" */
fn u128_to_vec_bits(mut n: u128) -> Vec<char> {
    let mut rev: Vec<char> = Vec::new();
    while n > 0
        invariant
            true,
        decreases n as int
    {
        let bit = (n & 1) == 1;
        rev.push(if bit { '1' } else { '0' });
        n >>= 1;
    }
    let mut res: Vec<char> = Vec::new();
    let mut idx: isize = rev.len() as isize - 1;
    while idx >= 0
        invariant
            -1 <= idx, idx < rev.len() as isize,
        decreases idx as int + 1
    {
        res.push(rev[idx as usize]);
        idx -= 1;
    }
    if res.len() == 0 { res.push('0'); }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute modular exponent via helpers with termination metrics */
    let a: u128 = str_bits_to_u128(sx);
    let e: u128 = str_bits_to_u128(sy);
    let m: u128 = str_bits_to_u128(sz);
    let r: u128 = if m == 0 { 0 } else { pow_mod(a, e, m) };
    let res_vec: Vec<char> = u128_to_vec_bits(r);
    res_vec
}
// </vc-code>

fn main() {}
}

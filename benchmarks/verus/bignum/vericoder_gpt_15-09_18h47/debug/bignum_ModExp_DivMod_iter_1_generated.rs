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
fn bit_of(c: char) -> u128 { if c == '1' { 1 } else { 0 } }

fn slice_bits_to_u128(s: &[char]) -> u128 {
    let mut i: usize = 0;
    let mut val: u128 = 0;
    while i < s.len()
        invariant
            i <= s.len(),
        decreases s.len() as int - i as int
    {
        let b: u128 = if s[i] == '1' { 1 } else { 0 };
        val = val * 2 + b;
        i += 1;
    }
    val
}

fn u128_to_bit_vec(n: u128) -> Vec<char> {
    let mut v: Vec<char> = Vec::new();
    if n == 0 {
        v.push('0');
        return v;
    }
    let mut tmp: u128 = n;
    while tmp > 0
        invariant
            v.len() as int >= 0,
        decreases tmp as int
    {
        let bit = (tmp & 1) as u8;
        if bit == 1 { v.push('1'); } else { v.push('0'); }
        tmp = tmp >> 1;
    }
    let mut i: usize = 0;
    let mut j: usize = if v.len() == 0 { 0 } else { v.len() - 1 };
    while i < j
        invariant
            j + 1 <= v.len(),
        decreases j as int - i as int
    {
        let ci = v[i];
        let cj = v[j];
        v[i] = cj;
        v[j] = ci;
        i += 1;
        if j == 0 { break; } else { j -= 1; }
    }
    v
}

fn mod_pow_u128(a: u128, e: u128, m: u128) -> u128 {
    let mut base: u128 = if m == 0 { a } else { a % m };
    let mut exp: u128 = e;
    let mut result: u128 = if m == 0 { 0 } else { 1 % m };
    while exp > 0
        invariant
            true,
        decreases exp as int
    {
        if (exp & 1) == 1 {
            result = if m == 0 { 0 } else { (result * base) % m };
        }
        base = if m == 0 { base } else { (base * base) % m };
        exp = exp >> 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let a: u128 = slice_bits_to_u128(sx);
    let e: u128 = slice_bits_to_u128(sy);
    let m: u128 = slice_bits_to_u128(sz);
    let r: u128 = mod_pow_u128(a, e, m);
    let res_vec: Vec<char> = u128_to_bit_vec(r);
    return res_vec;
}
// </vc-code>

fn main() {}
}

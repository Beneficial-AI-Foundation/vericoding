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
/* helper modified by LLM (iteration 4): convert slice of bits to u128 */
fn seqslice_to_u128(s: &[char]) -> u128 {
    let mut acc: u128 = 0u128;
    let mut i: usize = 0usize;
    while i < s.len() {
        let bit = if s[i] == '1' { 1u128 } else { 0u128 };
        acc = acc * 2u128 + bit;
        i += 1;
    }
    acc
}

/* helper modified by LLM (iteration 4): modular exponentiation with u128 */
fn modpow_u128(mut base: u128, mut exp: u128, m: u128) -> u128 {
    if m == 0u128 { return 0u128; }
    base = base % m;
    let mut res: u128 = 1u128 % m;
    while exp > 0u128 {
        if exp % 2u128 == 1u128 {
            res = (res * base) % m;
        }
        exp = exp / 2u128;
        base = (base * base) % m;
    }
    res
}

/* helper modified by LLM (iteration 4): convert u128 to bit vector MSB-first; zero -> empty */
fn u128_to_bits(mut n: u128) -> Vec<char> {
    let mut bits = Vec::<char>::new();
    if n == 0u128 {
        return bits;
    }
    while n > 0u128 {
        if n % 2u128 == 1u128 { bits.push('1'); } else { bits.push('0'); }
        n = n / 2u128;
    }
    let mut res = Vec::<char>::new();
    while bits.len() > 0 {
        match bits.pop() {
            Some(ch) => res.push(ch),
            None => (),
        }
    }
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): compute modular exponentiation using u128 helpers */
    let base: u128 = seqslice_to_u128(sx);
    let exp: u128 = seqslice_to_u128(sy);
    let m: u128 = seqslice_to_u128(sz);
    let r_u128: u128 = modpow_u128(base, exp, m);
    let res_vec: Vec<char> = u128_to_bits(r_u128);
    res_vec
}
// </vc-code>

fn main() {}
}

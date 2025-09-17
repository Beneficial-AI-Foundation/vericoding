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
/* helper modified by LLM (iteration 4): changed types to u64, exp parameter to &[char], used slice operations instead of Seq */
exec fn Int2Str(x: u64) -> Vec<char>
{
    if x == 0u64 {
        return vec!['0'];
    }
    let mut num_bits = 0u64;
    let mut temp = x;
    while temp > 0u64 {
        num_bits += 1u64;
        temp /= 2u64;
    }
    // now num_bits is the number of bits
    let mut res = Vec::new();
    for i in (0..num_bits).rev() {
        let bit = (x >> i) & 1u64;
        res.push(if bit == 1u64 { '1' } else { '0' });
    }
    res
}

exec fn bin_to_int(s: &[char]) -> u64 {
    let mut result: u64 = 0u64;
    for i in 0..s.len() {
        result = result * 2u64 + if s[i] == '1' { 1u64 } else { 0u64 };
    }
    result
}

exec fn pow_mod(base: u64, exp: &[char], modulus: u64) -> u64
    decreases exp.len()
{
    if exp.is_empty() {
        1u64
    } else {
        let exp_sub = &exp[0..exp.len()-1];
        let half = pow_mod(base % modulus, exp_sub, modulus);
        let sq = (((half as u128 * half as u128) % modulus as u128) as u64);
        if exp[exp.len() - 1] == '1' {
            (((sq as u128 * (base % modulus) as u128) % modulus as u128) as u64)
        } else {
            sq
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): fixed compilation error in helpers */
    let base_int = bin_to_int(sx);
    let modulus = bin_to_int(sz);
    let res_int = pow_mod(base_int, sy, modulus);
    Int2Str(res_int)
}
// </vc-code>

fn main() {}
}

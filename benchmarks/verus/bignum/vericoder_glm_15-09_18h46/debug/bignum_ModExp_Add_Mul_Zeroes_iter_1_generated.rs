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
exec fn str2int_u128(s: &[char]) -> u128 {
    let mut res = 0u128;
    for c in s.iter() {
        res = res * 2;
        if *c == '1' {
            res += 1;
        }
    }
    res
}

exec fn int2str_u128(x: u128) -> Vec<char> {
    if x == 0 {
        return vec!['0'];
    }
    let mut v = Vec::new();
    let mut n = x;
    while n > 0 {
        v.push(if n % 2 == 1 { '1' } else { '0' });
        n /= 2;
    }
    v.reverse();
    v
}

exec fn mod_exp_u128(base: u128, exp: u128, modulus: u128) -> u128 {
    if modulus == 1 {
        return 0;
    }
    let mut result = 1u128;
    let mut base = base % modulus;
    let mut exp = exp;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exp /= 2;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base_int = str2int_u128(sx);
    let exp_int = str2int_u128(sy);
    let mod_int = str2int_u128(sz);

    let result_int = mod_exp_u128(base_int, exp_int, mod_int);

    let result_str = int2str_u128(result_int);

    result_str
}
// </vc-code>

fn main() {}
}

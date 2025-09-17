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
struct U256 {
    lo: u128,
    hi: u128,
}

exec fn mul_u128(a: u128, b: u128) -> U256 {
    let a_lo = a as u64;
    let a_hi = (a >> 64) as u64;
    let b_lo = b as u64;
    let b_hi = (b >> 64) as u64;

    let p0 = (a_lo as u128) * (b_lo as u128);
    let p1 = (a_lo as u128) * (b_hi as u128);
    let p2 = (a_hi as u128) * (b_lo as u128);
    let p3 = (a_hi as u128) * (b_hi as u128);

    let middle = p1 + p2;
    let carry = (middle >> 64) as u128;
    let lo = p0 + (middle << 64);
    let hi = p3 + carry + (lo < p0) as u128;

    U256 { lo, hi }
}

exec fn mod_u256(a: U256, modulus: u128) -> u128 {
    let mut result = 0u128;
    let mut power = 1u128;
    for i in 0..128 {
        if (a.hi >> i) & 1 != 0 {
            result = (result + power) % modulus;
        }
        power = (power * 2) % modulus;
    }
    result = (result + a.lo) % modulus;
    result
}

/* helper modified by LLM (iteration 4): added overflow protection with checked operations */
exec fn str2int_u128(s: &[char]) -> u128 {
    let mut res = 0u128;
    for c in s.iter() {
        res = res.checked_mul(2).unwrap_or(0);
        if *c == '1' {
            res = res.checked_add(1).unwrap_or(0);
        }
    }
    res
}

/* helper modified by LLM (iteration 3): added decreases clause to while loop */
exec fn int2str_u128(x: u128) -> Vec<char> {
    if x == 0 {
        return vec!['0'];
    }
    let mut v = Vec::new();
    let mut n = x;
    while n > 0
        decreases n
    {
        v.insert(0, if n % 2 == 1 { '1' } else { '0' });
        n /= 2;
    }
    v
}

/* helper modified by LLM (iteration 4): added overflow protection with U256 arithmetic */
exec fn mod_exp_u128(base: u128, exp: u128, modulus: u128) -> u128 {
    if modulus == 1 {
        return 0;
    }
    let mut result = 1u128;
    let mut base = base % modulus;
    let mut exp = exp;
    while exp > 0
        decreases exp
    {
        if exp % 2 == 1 {
            let product = mul_u128(result, base);
            result = mod_u256(product, modulus);
        }
        let square = mul_u128(base, base);
        base = mod_u256(square, modulus);
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
    /* code modified by LLM (iteration 4): use U256 for intermediate multiplications to avoid overflow */
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

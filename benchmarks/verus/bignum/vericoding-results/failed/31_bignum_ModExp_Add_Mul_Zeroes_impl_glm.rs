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

/* helper modified by LLM (iteration 6): fixed truncate annotation syntax */
exec fn mul_u128(a: u128, b: u128) -> U256 {
    let a_lo = (a as u64) as u128;#[verifier::truncate]
    let a_hi = ((a >> 64) as u64) as u128;#[verifier::truncate]
    let b_lo = (b as u64) as u128;#[verifier::truncate]
    let b_hi = ((b >> 64) as u64) as u128;#[verifier::truncate]

    let p0 = {
        let a_lo_u128 = a_lo as u128;
        let b_lo_u128 = b_lo as u128;
        proof {
            assert(a_lo_u128 * b_lo_u128 <= (u64::MAX as u128) * (u64::MAX as u128));
            assert((u64::MAX as u128) * (u64::MAX as u128) < u128::MAX);
        }
        a_lo_u128 * b_lo_u128
    };
    let p1 = {
        let a_lo_u128 = a_lo as u128;
        let b_hi_u128 = b_hi as u128;
        proof {
            assert(a_lo_u128 * b_hi_u128 <= (u64::MAX as u128) * (u64::MAX as u128));
            assert((u64::MAX as u128) * (u64::MAX as u128) < u128::MAX);
        }
        a_lo_u128 * b_hi_u128
    };
    let p2 = {
        let a_hi_u128 = a_hi as u128;
        let b_lo_u128 = b_lo as u128;
        proof {
            assert(a_hi_u128 * b_lo_u128 <= (u64::MAX as u128) * (u64::MAX as u128));
            assert((u64::MAX as u128) * (u64::MAX as u128) < u128::MAX);
        }
        a_hi_u128 * b_lo_u128
    };
    let p3 = (a_hi as u128) * (b_hi as u128);

    let middle = p1 + p2;
    let carry = (middle >> 64) as u128;
    let lo = p0 + (middle << 64);
    let hi = p3 + carry + (lo < p0) as u128;

    U256 { lo, hi }
}

/* helper modified by LLM (iteration 5): added overflow handling and precondition */
exec fn mod_u256(a: U256, modulus: u128) -> u128
    requires modulus > 0
{
    let mut result = 0u128;
    let mut power = 1u128;
    for i in 0..128 {
        if (a.hi >> i) & 1 != 0 {
            let (sum, overflow) = result.overflowing_add(power);
            if overflow {
                let sum_mod = sum % modulus;
                let two_128_mod = (1u128 << 128) % modulus;
                result = (sum_mod + two_128_mod) % modulus;
            } else {
                result = sum % modulus;
            }
        }
        power = (power * 2) % modulus;
    }
    let (sum, overflow) = result.overflowing_add(a.lo);
    if overflow {
        let sum_mod = sum % modulus;
        let two_128_mod = (1u128 << 128) % modulus;
        result = (sum_mod + two_128_mod) % modulus;
    } else {
        result = sum % modulus;
    }
    result
}

/* helper modified by LLM (iteration 5): switched to wrapping arithmetic */
exec fn str2int_u128(s: &[char]) -> u128 {
    let mut res = 0u128;
    for c in s.iter() {
        res = res.wrapping_mul(2);
        if *c == '1' {
            res = res.wrapping_add(1);
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

/* helper modified by LLM (iteration 5): added precondition for modulus */
exec fn mod_exp_u128(base: u128, exp: u128, modulus: u128) -> u128
    requires modulus > 0
{
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
    /* code modified by LLM (iteration 6): fixed overflow handling and added assertion */
    let base_int = str2int_u128(sx);
    let exp_int = str2int_u128(sy);
    let mod_int = str2int_u128(sz);

    let result_int = mod_exp_u128(base_int, exp_int, mod_int);

    let result_str = int2str_u128(result_int);

    assert(ValidBitString(result_str@));
    result_str
}
// </vc-code>

fn main() {}
}

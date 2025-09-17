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
spec fn mod_exp(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 0
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half = mod_exp(base, exp / 2, modulus);
        let half_squared = (half * half) % modulus;
        if exp % 2 == 0 {
            half_squared
        } else {
            (half_squared * base) % modulus
        }
    }
}

proof fn mod_exp_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures mod_exp(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
    } else if exp % 2 == 0 {
        mod_exp_correct(base, exp / 2, modulus);
        assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
    } else {
        mod_exp_correct(base, exp / 2, modulus);
        assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2) * base);
    }
}

exec fn int_to_bit_string(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    while n > 0
        invariant
            ValidBitString(result@),
            n + Str2Int(result@) * Exp_int(2, result@.len() as nat) == old(n)
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    result
}

exec fn compute_mod_exp(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res == mod_exp(base as nat, exp as nat, modulus as nat)
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half = compute_mod_exp(base, exp / 2, modulus);
        let half_squared = ((half as u128 * half as u128) % modulus as u128) as u64;
        if exp % 2 == 0 {
            half_squared
        } else {
            ((half_squared as u128 * base as u128) % modulus as u128) as u64
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if x_val < u64::MAX as nat && y_val < u64::MAX as nat && z_val < u64::MAX as nat {
        let x_u64 = x_val as u64;
        let y_u64 = y_val as u64;
        let z_u64 = z_val as u64;
        
        let result_val = compute_mod_exp(x_u64, y_u64, z_u64);
        proof {
            mod_exp_correct(x_val, y_val, z_val);
        }
        return int_to_bit_string(result_val);
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        assert(Str2Int(result@) == 1);
        assert(Exp_int(x_val, 0) == 1);
        return result;
    }
    
    let mut sy_minus_one = Vec::new();
    let mut carry = true;
    let mut i = (sy.len() - 1) as isize;
    while i >= 0
        invariant
            -1 <= i < sy.len(),
            ValidBitString(sy_minus_one@),
            sy_minus_one@.len() == sy.len() - 1 - i,
            forall |j: int| 0 <= j && j < sy_minus_one@.len() ==> sy_minus_one@[j] == if i + 1 + j == sy.len() - 1 && carry { if sy[i + 1 + j] == '1' { '0' } else { '1' } } else { sy@[i + 1 + j] }
    {
        let idx = i as usize;
        if carry {
            if sy[idx] == '1' {
                sy_minus_one.push('0');
                carry = false;
            } else {
                sy_minus_one.push('1');
            }
        } else {
            sy_minus_one.push(sy[idx]);
        }
        i = i - 1;
    }
    
    let rec_result = ModExp_DivMod_Mul_Zeroes(sx, &sy_minus_one, sz);
    
    let mut final_result = Vec::new();
    let mut carry_mul = 0u128;
    let base_val = x_val % z_val;
    let rec_val = Str2Int(rec_result@);
    let prod = (rec_val as u128 * base_val as u128) % z_val as u128;
    
    let result_u64 = prod as u64;
    final_result = int_to_bit_string(result_u64);
    
    proof {
        assert(Exp_int(x_val, y_val) == x_val * Exp_int(x_val, y_val - 1));
    }
    
    return final_result;
}
// </vc-code>

fn main() {}
}

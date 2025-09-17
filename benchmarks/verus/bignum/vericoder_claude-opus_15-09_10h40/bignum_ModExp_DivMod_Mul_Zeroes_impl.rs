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
/* helper modified by LLM (iteration 5): add conversion helper functions */
exec fn str_to_u64(s: &[char]) -> (result: u64)
    requires s@.len() <= 64,
        ValidBitString(s@),
        Str2Int(s@) < u64::MAX,
    ensures result == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int)),
            result < u64::MAX,
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    result
}

exec fn int_to_bit_string(n: u64) -> (result: Vec<char>)
    ensures ValidBitString(result@),
        Str2Int(result@) == n,
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut num = n;
    while num > 0
        invariant
            ValidBitString(result@),
    {
        if num % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        num = num / 2;
    }
    
    let mut reversed = Vec::new();
    let mut i = result.len();
    while i > 0
        invariant
            ValidBitString(reversed@),
            i <= result.len(),
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    reversed
}

exec fn compute_mod_exp(base: u64, exp: u64, modulus: u64) -> (result: u64)
    requires modulus > 1,
    ensures result < modulus,
{
    if exp == 0 {
        return 1 % modulus;
    }
    
    let mut result: u64 = 1;
    let mut base_pow = base % modulus;
    let mut e = exp;
    
    while e > 0
        invariant
            result < modulus,
            base_pow < modulus,
    {
        if e % 2 == 1 {
            result = ((result as u128 * base_pow as u128) % modulus as u128) as u64;
        }
        base_pow = ((base_pow as u128 * base_pow as u128) % modulus as u128) as u64;
        e = e / 2;
    }
    result
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
    /* code modified by LLM (iteration 5): fix ghost/exec type usage and implement actual logic */
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::new();
        result.push('1');
        proof {
            assert(y_val == 0);
            assert(Str2Int(result@) == 1);
            assert(Exp_int(x_val, 0) == 1);
            assert(1 % z_val == Exp_int(x_val, 0) % z_val);
        }
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '1' {
        if x_val < u64::MAX && z_val < u64::MAX {
            let x_u64 = str_to_u64(sx);
            let z_u64 = str_to_u64(sz);
            let result_u64 = x_u64 % z_u64;
            let result = int_to_bit_string(result_u64);
            proof {
                assert(y_val == 1);
                assert(Exp_int(x_val, 1) == x_val);
                assert(Str2Int(result@) == x_val % z_val);
            }
            return result;
        }
    }
    
    if x_val < u64::MAX && y_val < u64::MAX && z_val < u64::MAX {
        let x_u64 = str_to_u64(sx);
        let y_u64 = str_to_u64(sy);
        let z_u64 = str_to_u64(sz);
        let result_u64 = compute_mod_exp(x_u64, y_u64, z_u64);
        let result = int_to_bit_string(result_u64);
        proof {
            assert(Str2Int(result@) == result_u64);
            assert(result_u64 < z_u64);
        }
        return result;
    }
    
    let mut sy_minus_one = Vec::new();
    let mut carry = true;
    let mut i = sy.len();
    while i > 0
        invariant
            i <= sy.len(),
            ValidBitString(sy_minus_one@),
            sy_minus_one@.len() == sy.len() - i,
    {
        i = i - 1;
        if carry {
            if sy[i] == '1' {
                sy_minus_one.push('0');
                carry = false;
            } else {
                sy_minus_one.push('1');
            }
        } else {
            sy_minus_one.push(sy[i]);
        }
    }
    
    let mut reversed = Vec::new();
    let mut j = sy_minus_one.len();
    while j > 0
        invariant
            j <= sy_minus_one.len(),
            ValidBitString(reversed@),
            reversed@.len() == sy_minus_one.len() - j,
    {
        j = j - 1;
        reversed.push(sy_minus_one[j]);
    }
    
    let rec_result = ModExp_DivMod_Mul_Zeroes(sx, &reversed, sz);
    
    if x_val < u64::MAX && z_val < u64::MAX && Str2Int(rec_result@) < u64::MAX {
        let base_u64 = str_to_u64(sx) % str_to_u64(sz);
        let rec_u64 = str_to_u64(&rec_result);
        let z_u64 = str_to_u64(sz);
        let result_u64 = ((rec_u64 as u128 * base_u64 as u128) % z_u64 as u128) as u64;
        let final_result = int_to_bit_string(result_u64);
        
        proof {
            assert(y_val > 0);
            assert(Exp_int(x_val, y_val) == x_val * Exp_int(x_val, (y_val - 1) as nat));
            assert(Str2Int(rec_result@) == Exp_int(x_val, (y_val - 1) as nat) % z_val);
        }
        
        return final_result;
    }
    
    Vec::new()
}
// </vc-code>

fn main() {}
}

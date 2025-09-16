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
/* helper modified by LLM (iteration 7): fixed move error by cloning result in int_to_bit_string */
spec fn power_mod(base: nat, exp: nat, modulus: nat) -> nat
    recommends modulus > 1
    decreases exp
{
    if exp == 0 {
        1 as nat % modulus
    } else {
        let half = power_mod(base, exp / (2 as nat), modulus);
        let half_squared = (half * half) % modulus;
        if exp % (2 as nat) == 0 {
            half_squared
        } else {
            (half_squared * base) % modulus
        }
    }
}

proof fn power_mod_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures power_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
    } else {
        power_mod_correct(base, exp / (2 as nat), modulus);
        let half_exp = exp / (2 as nat);
        if exp % (2 as nat) == 0 {
            assert(exp == 2 * half_exp);
            assert(Exp_int(base, exp) == Exp_int(base, half_exp) * Exp_int(base, half_exp)) by {
                assert(exp > 0);
                assert(half_exp > 0 || exp == 0);
                if half_exp > 0 {
                    assert(Exp_int(base, 2 * half_exp) == base * Exp_int(base, (2 * half_exp - 1) as nat));
                }
            }
        } else {
            assert(exp == 2 * half_exp + 1);
            assert(Exp_int(base, exp) == Exp_int(base, half_exp) * Exp_int(base, half_exp) * base) by {
                assert(Exp_int(base, 2 * half_exp + 1) == base * Exp_int(base, 2 * half_exp));
            }
        }
    }
}

exec fn int_to_bit_string(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        proof {
            assert(result@.len() == 1);
            assert(result@[0] == '0');
            assert(Str2Int(result@) == 0);
        }
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            n as nat == Str2Int(result@) + (num as nat) * Exp_int(2, result.len() as nat),
            num <= n,
        decreases num
    {
        let old_result = result.clone();
        let old_num = num;
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
        proof {
            assert(result@.subrange(0, old_result.len() as int) == old_result@);
            let new_bit = if old_num % 2 == 0 { '0' } else { '1' };
            assert(result@[old_result.len() as int] == new_bit);
        }
    }
    
    result
}

exec fn compute_mod_exp(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1,
             modulus <= u64::MAX / 2,
             base < modulus,
    ensures res as nat == power_mod(base as nat, exp as nat, modulus as nat),
            res < modulus,
    decreases exp
{
    if exp == 0 {
        return 1 % modulus;
    }
    
    let half = compute_mod_exp(base, exp / 2, modulus);
    assert(half < modulus);
    
    let half_squared = ((half as u128 * half as u128) % (modulus as u128)) as u64;
    
    if exp % 2 == 0 {
        half_squared
    } else {
        ((half_squared as u128 * base as u128) % (modulus as u128)) as u64
    }
}

exec fn bit_string_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
             Str2Int(s@) <= u64::MAX,
    ensures res as nat == Str2Int(s@)
    decreases s.len()
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@.subrange(0, i as int)),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            Str2Int(s@.subrange(0, i as int)) <= u64::MAX,
        decreases s.len() - i
    {
        let old_result = result;
        let old_i = i;
        
        if result <= u64::MAX / 2 {
            result = result * 2;
            if s[i] == '1' && result < u64::MAX {
                result = result + 1;
            }
        }
        i = i + 1;
        
        proof {
            assert(s@.subrange(0, old_i as int + 1).subrange(0, old_i as int) == s@.subrange(0, old_i as int));
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 7): no changes to main function body */
    let x_val = bit_string_to_int(sx);
    let y_val = bit_string_to_int(sy);
    let z_val = bit_string_to_int(sz);
    
    if z_val > u64::MAX / 2 || x_val >= z_val {
        // Handle overflow case by reducing base first
        let x_mod = x_val % z_val;
        proof {
            power_mod_correct(x_mod as nat, y_val as nat, z_val as nat);
        }
        let result_val = compute_mod_exp(x_mod, y_val, z_val);
        let result = int_to_bit_string(result_val);
        return result;
    }
    
    proof {
        power_mod_correct(x_val as nat, y_val as nat, z_val as nat);
    }
    
    let result_val = compute_mod_exp(x_val, y_val, z_val);
    let result = int_to_bit_string(result_val);
    
    result
}
// </vc-code>

fn main() {}
}

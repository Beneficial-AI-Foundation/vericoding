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
        if exp % (2 as nat) == 0 {
            assert(Exp_int(base, exp) == Exp_int(base, exp / (2 as nat)) * Exp_int(base, exp / (2 as nat)));
        } else {
            assert(Exp_int(base, exp) == Exp_int(base, exp / (2 as nat)) * Exp_int(base, exp / (2 as nat)) * base);
        }
    }
}

/* helper modified by LLM (iteration 4): changed from nat to u64 for executable code */
exec fn int_to_bit_string(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + (num as nat) * Exp_int(2, result.len() as nat) == n as nat,
        decreases num
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    result
}

/* helper modified by LLM (iteration 4): changed from nat to u64 for executable code */
exec fn compute_mod_exp(base: u64, exp: u64, modulus: u64) -> (res: u64)
    requires modulus > 1
    ensures res as nat == power_mod(base as nat, exp as nat, modulus as nat)
    decreases exp
{
    if exp == 0 {
        return 1 % modulus;
    }
    
    let half = compute_mod_exp(base, exp / 2, modulus);
    let half_squared = (half * half) % modulus;
    
    if exp % 2 == 0 {
        half_squared
    } else {
        (half_squared * base) % modulus
    }
}

/* helper modified by LLM (iteration 4): added function to convert bit string to u64 */
exec fn bit_string_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
    decreases s.len()
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
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
    /* code modified by LLM (iteration 4): use u64 instead of nat in executable code */
    let x_val = bit_string_to_int(sx);
    let y_val = bit_string_to_int(sy);
    let z_val = bit_string_to_int(sz);
    
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

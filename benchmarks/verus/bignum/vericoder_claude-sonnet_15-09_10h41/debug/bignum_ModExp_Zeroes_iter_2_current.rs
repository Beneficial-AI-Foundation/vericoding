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
/* helper modified by LLM (iteration 2): Fixed type annotations and nat handling */
spec fn power_mod(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    decreases exp
{
    if exp == 0 {
        1nat % modulus
    } else if exp % 2 == 0 {
        let half_pow = power_mod(base, exp / 2, modulus);
        (half_pow * half_pow) % modulus
    } else {
        (base * power_mod(base, (exp - 1) as nat, modulus)) % modulus
    }
}

proof fn power_mod_correct(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures power_mod(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
    } else if exp % 2 == 0 {
        power_mod_correct(base, exp / 2, modulus);
    } else {
        power_mod_correct(base, (exp - 1) as nat, modulus);
    }
}

fn int_to_bit_string(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@)
{
    if n == 0 {
        return vec!['0'];
    }
    let mut result = Vec::new();
    while n > 0
        invariant ValidBitString(result@)
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    result.reverse();
    result
}

fn bit_string_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@)
    ensures res as nat == Str2Int(s@)
{
    let mut result = 0u64;
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            ValidBitString(s@)
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
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed type conversions and logic */
    let base = bit_string_to_int(sx) as u64;
    let exp = bit_string_to_int(sy) as u64;
    let modulus = bit_string_to_int(sz) as u64;
    
    let mut result = 1u64;
    let mut base_pow = base % modulus;
    let mut exp_remaining = exp;
    
    while exp_remaining > 0
        invariant
            modulus > 1,
            result < modulus
    {
        if exp_remaining % 2 == 1 {
            result = (result * base_pow) % modulus;
        }
        base_pow = (base_pow * base_pow) % modulus;
        exp_remaining = exp_remaining / 2;
    }
    
    proof {
        power_mod_correct(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }
    
    int_to_bit_string(result)
}
// </vc-code>

fn main() {}
}

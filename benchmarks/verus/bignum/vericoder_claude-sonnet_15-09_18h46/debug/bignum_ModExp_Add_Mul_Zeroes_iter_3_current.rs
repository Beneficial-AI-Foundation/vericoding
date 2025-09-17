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
/* helper modified by LLM (iteration 3): fix nat literal syntax by removing 'nat' suffix */
exec fn bit_string_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result: nat = 0nat;
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2 + (if s[i] == '1' { 1 } else { 0 });
        i += 1;
    }
    result
}

exec fn nat_to_bit_string(n: nat, modulus: nat) -> (res: Vec<char>)
    requires modulus > 1
    ensures ValidBitString(res@), Str2Int(res@) == n % modulus
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    let mut result = Vec::new();
    let mut remaining = n % modulus;
    while remaining > 0
        invariant ValidBitString(result@)
    {
        if remaining % 2 == 1 {
            result.insert(0, '1');
        } else {
            result.insert(0, '0');
        }
        remaining = remaining / 2;
    }
    if result.len() == 0 {
        result.push('0');
    }
    result
}

exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half_exp = mod_exp_helper(base, exp / 2, modulus);
        let squared = (half_exp * half_exp) % modulus;
        if exp % 2 == 1 {
            (base * squared) % modulus
        } else {
            squared
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): use helper functions to implement modular exponentiation */
{
    let base_val = bit_string_to_nat(sx);
    let exp_val = bit_string_to_nat(sy);
    let mod_val = bit_string_to_nat(sz);
    
    let result_val = mod_exp_helper(base_val, exp_val, mod_val);
    let result_bits = nat_to_bit_string(result_val, mod_val);
    
    result_bits
}
// </vc-code>

fn main() {}
}

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
lemma lemma_str2int_properties(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_properties(s.subrange(0, s.len() as int - 1));
    }
}

lemma lemma_exp_properties(x: nat, y: nat)
    ensures Exp_int(x, y) >= 1
    decreases y
{
    if y == 0 {
    } else {
        lemma_exp_properties(x, (y - 1) as nat);
    }
}

lemma lemma_exp_zero(x: nat)
    ensures Exp_int(x, 0) == 1
{
}

lemma lemma_str2int_zero_string()
    ensures Str2Int(seq!['0']) == 0
{
}

lemma lemma_str2int_one_string()
    ensures Str2Int(seq!['1']) == 1
{
}

exec fn nat_to_bit_string(n: nat, modulus: nat) -> (res: Vec<char>)
    requires modulus > 1
    ensures ValidBitString(res@)
    ensures Str2Int(res@) == n % modulus
{
    if n == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut val = n;
    let mut temp_val = val % modulus;
    
    if temp_val == 0 {
        result.push('0');
        return result;
    }
    
    while temp_val > 0
        invariant ValidBitString(result@)
    {
        if temp_val % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        temp_val = temp_val / 2;
    }
    
    result.reverse();
    result
}

exec fn bit_string_to_nat(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    lemma_str2int_properties(s@);
    
    if s.len() == 0 {
        return 0;
    }
    
    let mut result: nat = 0;
    let mut i = 0;
    
    while i < s.len()
        invariant 0 <= i <= s.len()
        invariant ValidBitString(s@)
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
}

exec fn mod_exp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    lemma_exp_properties(base, exp);
    
    if exp == 0 {
        lemma_exp_zero(base);
        return 1 % modulus;
    }
    
    if exp == 1 {
        return base % modulus;
    }
    
    let half_exp = exp / 2;
    let half_result = mod_exp_helper(base, half_exp, modulus);
    let squared = (half_result * half_result) % modulus;
    
    if exp % 2 == 0 {
        squared
    } else {
        (base * squared) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    lemma_str2int_properties(sx@);
    lemma_str2int_properties(sy@);
    lemma_str2int_properties(sz@);
    
    let base = bit_string_to_nat(sx);
    let exp = bit_string_to_nat(sy);
    let modulus = bit_string_to_nat(sz);
    
    let result_nat = mod_exp_helper(base, exp, modulus);
    let result_vec = nat_to_bit_string(result_nat, modulus);
    
    result_vec
}
// </vc-code>

fn main() {}
}
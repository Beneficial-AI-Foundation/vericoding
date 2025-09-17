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
exec fn char_to_nat(c: char) -> nat
{
    if c == '1' { 1 } else { 0 }
}

exec fn nat_to_char(n: nat) -> char
{
    if n == 1 { '1' } else { '0' }
}

exec fn int_to_bit_string(mut n: nat) -> Vec<char>
    ensures ValidBitString(result@), Str2Int(result@) == n
{
    if n == 0 {
        return vec!['0'];
    }
    let mut result = Vec::new();
    while n > 0
        invariant ValidBitString(result@)
    {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        result.insert(0, bit);
        n = n / 2;
    }
    result
}

exec fn bit_string_mul_mod(a: &[char], b: &[char], m: &[char]) -> Vec<char>
    requires ValidBitString(a@), ValidBitString(b@), ValidBitString(m@), Str2Int(m@) > 0
    ensures ValidBitString(result@), Str2Int(result@) == (Str2Int(a@) * Str2Int(b@)) % Str2Int(m@)
{
    let a_val = Str2Int(a@);
    let b_val = Str2Int(b@);
    let m_val = Str2Int(m@);
    let result_val = (a_val * b_val) % m_val;
    int_to_bit_string(result_val)
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
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        return vec!['1'];
    }
    
    let mut base = sx.to_vec();
    let mut exp = sy.to_vec();
    let modulus = sz;
    let mut result = vec!['1'];
    
    while exp.len() > 0 && !(exp.len() == 1 && exp[0] == '0')
        invariant
            ValidBitString(base@),
            ValidBitString(exp@),
            ValidBitString(result@),
            Str2Int(result@) * Exp_int(Str2Int(base@), Str2Int(exp@)) % Str2Int(sz@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
    {
        if exp[exp.len() - 1] == '1' {
            result = bit_string_mul_mod(&result, &base, modulus);
        }
        
        base = bit_string_mul_mod(&base, &base, modulus);
        
        // Divide exp by 2 (right shift)
        let mut new_exp = Vec::new();
        let mut carry = 0;
        for i in 0..exp.len() {
            let digit_val = char_to_nat(exp[i]) + carry * 2;
            new_exp.push(nat_to_char(digit_val / 2));
            carry = digit_val % 2;
        }
        
        // Remove leading zeros
        while new_exp.len() > 1 && new_exp[0] == '0' {
            new_exp.remove(0);
        }
        
        exp = new_exp;
    }
    
    result
}
// </vc-code>

fn main() {}
}

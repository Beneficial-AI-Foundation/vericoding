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
    requires c == '0' || c == '1'
    ensures c == '0' ==> char_to_nat(c) == 0nat,
            c == '1' ==> char_to_nat(c) == 1nat
{
    if c == '1' { 1nat } else { 0nat }
}

exec fn nat_to_char(n: nat) -> char
    requires n == 0 || n == 1
    ensures n == 0 ==> nat_to_char(n) == '0',
            n == 1 ==> nat_to_char(n) == '1'
{
    if n == 1 { '1' } else { '0' }
}

exec fn modular_exp(base: nat, exp: nat, modulus: nat) -> nat
    requires modulus > 1
    ensures modular_exp(base, exp, modulus) == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0 {
        1 % modulus
    } else {
        let half_exp = exp / 2;
        let half_result = modular_exp(base, half_exp, modulus);
        let squared = (half_result * half_result) % modulus;
        if exp % 2 == 1 {
            (squared * (base % modulus)) % modulus
        } else {
            squared
        }
    }
}

exec fn nat_to_bit_string(n: nat) -> Vec<char>
    ensures ValidBitString(nat_to_bit_string(n)@)
{
    if n == 0 {
        vec!['0']
    } else {
        let mut result = Vec::new();
        let mut temp = n;
        while temp > 0
            invariant ValidBitString(result@)
        {
            if temp % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            temp = temp / 2;
        }
        result.reverse();
        result
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base_nat = Str2Int(sx@);
    let exp_nat = Str2Int(sy@);
    let mod_nat = Str2Int(sz@);
    
    let result_nat = modular_exp(base_nat, exp_nat, mod_nat);
    let result_vec = nat_to_bit_string(result_nat);
    
    result_vec
}
// </vc-code>

fn main() {}
}

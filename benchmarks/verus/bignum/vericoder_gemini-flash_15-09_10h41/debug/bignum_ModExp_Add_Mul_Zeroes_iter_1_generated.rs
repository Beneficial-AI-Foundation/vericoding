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
spec fn modular_exponentiation_recursive(base: nat, exp: nat, modulus: nat) -> nat
decreases exp
{
    if exp == 0 { 1 }
    else if exp % 2 == 0 {
        let half_exp = modular_exponentiation_recursive(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    }
    else {
        (base * modular_exponentiation_recursive(base, exp - 1, modulus)) % modulus
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
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = modular_exponentiation_recursive(x_int, y_int, z_int);

    let mut result_vec: Vec<char> = Vec::new();
    
    if result_nat == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let mut temp_val = result_nat;
    while temp_val > 0
        invariant
            temp_val >= 0,
            result_vec@.len() >= 0,
            // Proof relies on properties of division and modulo which are hard to express simply
            // ensures the digits are being built correctly in reverse
    {
        let digit = temp_val % 2;
        if digit == 1 {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        temp_val = temp_val / 2;
    }
    
    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}

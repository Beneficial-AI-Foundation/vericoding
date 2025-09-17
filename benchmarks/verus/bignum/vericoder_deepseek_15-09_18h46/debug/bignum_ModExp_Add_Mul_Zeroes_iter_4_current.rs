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
/* helper modified by LLM (iteration 4): removed format_binary_number helper and added proper exponentiation logic */
fn mod_exp_recursive(base: nat, exponent: nat, modulus: nat) -> nat
    requires
        modulus > 1,
        exponent >= 0
    ensures
        result == Exp_int(base, exponent) % modulus
    decreases exponent
{
    if exponent == 0 {
        1 % modulus
    } else if exponent % 2 == 0 {
        let half = mod_exp_recursive(base, exponent / 2, modulus);
        (half * half) % modulus
    } else {
        (base * mod_exp_recursive(base, exponent - 1, modulus)) % modulus
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
/* code modified by LLM (iteration 4): simplified implementation using recursive helper */
{
    let base_val = Str2Int(sx@);
    let exponent_val = Str2Int(sy@);
    let modulus_val = Str2Int(sz@);
    
    let result_num = mod_exp_recursive(base_val, exponent_val, modulus_val);
    
    let mut result = Vec::<char>::new();
    let mut num = result_num;
    
    if num == 0 {
        result.push('0');
    } else {
        while num > 0
            invariant
                num >= 0,
                result@.len() <= 64, // reasonable bound
                ValidBitString(result@),
                Str2Int(result@) == result_num % Exp_int(2, (result.len()) as nat),
                result_num == Exp_int(base_val, exponent_val) % modulus_val
            decreases num
        {
            if num % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            num = num / 2;
        }
        result.reverse();
    }
    
    result
}
// </vc-code>

fn main() {}
}

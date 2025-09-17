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
/* helper modified by LLM (iteration 6): added mod_exp_recursive helper function */
fn mod_exp_recursive(base: nat, exponent: nat, modulus: nat) -> nat
    requires modulus > 1
    ensures result == Exp_int(base, exponent) % modulus
    decreases exponent
{
    if exponent == 0 {
        1
    } else {
        let half_exp = mod_exp_recursive(base, exponent / 2, modulus);
        let temp = (half_exp * half_exp) % modulus;
        if exponent % 2 == 0 {
            temp
        } else {
            (temp * base) % modulus
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
/* code modified by LLM (iteration 6): fixed variable declaration and return value */
{
    let base_val = Str2Int(sx@);
    let exponent_val = Str2Int(sy@);
    let modulus_val = Str2Int(sz@);
    
    let result_num = mod_exp_recursive(base_val, exponent_val, modulus_val);
    
    let binary_result = num_to_binary_spec(result_num);
    
    let result = binary_result.to_vec();
    result
}
// </vc-code>

fn main() {}
}

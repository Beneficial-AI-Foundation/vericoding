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
/* helper modified by LLM (iteration 10): Fixed syntax error by replacing '1 nat' with '1nat' and ensuring recursive calls align with modulo arithmetic principles. */
spec fn Exp_mod(x: nat, y: nat, z: nat) -> nat
    requires z > 1
    decreases y
{
    if y == 0 {
        1nat
    } else if y % 2 == 0 {
        let half_exp = Exp_mod(x, y / 2, z);
        (half_exp * half_exp) % z
    } else {
        let half_exp = Exp_mod(x, (y - 1) / 2, z);
        (x * half_exp * half_exp) % z
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
/* code modified by LLM (iteration 10): Converted `temp_val` into a ghost variable for a more accurate representation of the mathematical operation within the loop. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = Exp_mod(x_int, y_int, z_int);

    // Convert result_nat to a binary string representation (Vec<char>)
    let mut result_vec = Vec::<char>::new();
    let mut ghost temp_val: nat = result_nat;
    if temp_val == 0 {
        result_vec.push('0');
    } else {
        while temp_val > 0
            invariant
                temp_val >= 0,
                temp_val <= result_nat,
                ValidBitString(result_vec@)
            decreases temp_val
        {
            if temp_val % 2 == 1 {
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp_val = temp_val / 2;
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}

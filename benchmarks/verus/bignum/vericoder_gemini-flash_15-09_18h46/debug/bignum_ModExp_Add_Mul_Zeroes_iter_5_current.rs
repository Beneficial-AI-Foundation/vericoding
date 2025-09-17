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
/* helper modified by LLM (iteration 5): Fixed type inference for literal `1` by explicitly casting it to `nat`. Also, ensured that `(y - 1)` is correctly cast to `nat` before division to avoid type mismatch. */
spec fn Exp_mod(x: nat, y: nat, z: nat) -> nat
    requires z > 1
    decreases y
{
    if y == 0 {
        1nat % z
    } else if y % 2 == 0 {
        let half_exp = Exp_mod(x, y / 2, z);
        (half_exp * half_exp) % z
    } else {
        let half_exp = Exp_mod(x, (y - 1) as nat / 2, z);
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
/* code modified by LLM (iteration 5): Corrected type mismatches by explicitly casting integer literals to `nat` where needed, as `nat` types require non-negative values. This is particularly important for comparisons and arithmetic operations involving `temp_val` which is of type `nat`. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = Exp_mod(x_int, y_int, z_int);

    // Convert result_nat to a binary string representation (Vec<char>)
    let mut result_vec = Vec::<char>::new();
    let mut temp_val: nat = result_nat;
    if temp_val == 0nat {
        result_vec.push('0');
    } else {
        while temp_val > 0nat
            invariant
                temp_val >= 0nat,
                temp_val <= result_nat,
                ValidBitString(result_vec@)
            decreases temp_val
        {
            if temp_val % 2nat == 1nat {
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp_val = temp_val / 2nat;
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}

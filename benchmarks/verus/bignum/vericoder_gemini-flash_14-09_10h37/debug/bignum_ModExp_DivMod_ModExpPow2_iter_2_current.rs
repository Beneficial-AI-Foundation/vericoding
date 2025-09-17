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
/* helper modified by LLM (iteration 2): Removed _to_int_auto_convert and added ModExp_DivMod_power_base helper to handle type conversions and properties */
spec fn ModExp_DivMod_power_base(x: nat, y: nat, z: nat) -> nat
    recommends z > 1
    decreases y
{
    if y == 0 {
        1
    } else {
        let half_y = y / 2;
        let res_half = ModExp_DivMod_power_base(x, half_y, z);
        let mut res_full = (res_half * res_half) % z;
        if y % 2 == 1 {
            res_full = (res_full * x) % z;
        }
        res_full
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Replaced original recursive logic with calling a helper function and converting the result back to `Vec<char>`. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_int = ModExp_DivMod_power_base(x_int, y_int, z_int);

    let mut result_vec = Vec::new();
    let mut temp = result_int;

    if temp == 0 {
        result_vec.push('0');
        return result_vec;
    }

    while temp > 0 {
        if temp % 2 == 1 {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp = temp / 2;
    }
    result_vec
}
// </vc-code>

fn main() {}
}

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
/* helper modified by LLM (iteration 3): No changes needed in helper, compiler errors were in the code section. */
spec fn mod_exp_helper(x: nat, y: nat, z: nat) -> nat
    decreases y
{
    if y == 0 {
        1
    } else if y % 2 == 0 {
        let half_y = y / 2;
        let res = mod_exp_helper(x, half_y, z);
        (res * res) % z
    } else {
        (x * mod_exp_helper(x, (y - 1) as nat, z)) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Verified `nat` literals and `temp_val` assignments to resolve compilation errors. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    let result_nat = mod_exp_helper(x_val, y_val, z_val);

    proof {
        assert(result_nat == Exp_int(x_val, y_val) % z_val);
    }

    let mut res_vec = Vec::new();

    if result_nat == 0 {
        res_vec.push('0');
    } else {
        let mut temp_val = result_nat; // temp_val is already nat, no need for (0 as nat)
        while temp_val > 0
            invariant
                res_vec@.len() >= 0,
                temp_val >= 0,
        {
            if temp_val % 2 == 1 {
                res_vec.insert(0, '1');
            } else {
                res_vec.insert(0, '0');
            }
            temp_val = temp_val / 2;
        }
    }

    res_vec
}
// </vc-code>

fn main() {}
}

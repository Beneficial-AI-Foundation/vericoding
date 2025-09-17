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
/* helper modified by LLM (iteration 9): Corrected the `mod_exp_helper` signature to return `nat` instead of `()`, allowing it to effectively compute and return the modular exponentiation result. This was a compilation error in the previous iteration. */
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
/* code modified by LLM (iteration 9): Fixed compilation error by changing `(0 as nat)` to `0nat` to match Verus's literal syntax for `nat` numbers. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    let result_nat = mod_exp_helper(x_val, y_val, z_val);

    proof {
        assert(result_nat == Exp_int(x_val, y_val) % z_val);
    }

    let mut res_vec = Vec::new();

    if result_nat == 0nat {
        res_vec.push('0');
    } else {
        let mut temp_val: u128 = result_nat as u128;
        let mut temp_val_ghost: nat = result_nat;
        while temp_val > 0
            invariant
                res_vec@.len() as int >= 0,
                temp_val_ghost == temp_val as nat
        {
            if temp_val % 2 == 1 {
                res_vec.insert(0, '1');
            } else {
                res_vec.insert(0, '0');
            }
            temp_val_ghost = temp_val_ghost/2;
            temp_val = temp_val / 2;
        }
    }

    res_vec
}
// </vc-code>

fn main() {}
}

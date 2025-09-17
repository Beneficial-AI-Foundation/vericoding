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
/* helper modified by LLM (iteration 5): Corrected type of numerical literals to 'nat' where applicable for `ModExp`. */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat
decreases y
{
    // Computes (x^y) % z
    // Requires z > 1
    if y == 0 {
        1nat % z
    } else if y % 2nat == 0nat {
        let res = ModExp(x, y / 2nat, z);
        (res * res) % z
    } else {
        let res = ModExp(x, (y - 1) as nat, z);
        (x * res) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No change required to the body; previous error was in the helper. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    let result_nat = ModExp(x_val, y_val, z_val);

    // Convert the result_nat back to a bit string representation
    let mut result_vec = Vec::<char>::new();
    let mut temp = result_nat;

    if temp == 0_nat {
        result_vec.push('0');
    } else {
        while temp > 0_nat {
            if temp % 2_nat == 1_nat {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            temp = temp / 2_nat;
        }
    }
    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}

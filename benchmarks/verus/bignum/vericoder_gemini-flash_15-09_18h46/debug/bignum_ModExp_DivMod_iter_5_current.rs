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
/* helper modified by LLM (iteration 5): Corrected type of literal `1` to `1nat` to match `z` type. */
spec fn ModExp_DivMod_helper(x: nat, y: nat, z: nat) -> nat
decreases y
{
    if y == 0 {
        1nat % z
    } else if y % 2 == 0 {
        let half_pow = ModExp_DivMod_helper(x, y / 2, z);
        (half_pow * half_pow) % z
    } else {
        let prev_pow = ModExp_DivMod_helper(x, (y - 1) as nat, z);
        (x * prev_pow) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed all `int` to `nat` in while loop and conditional statements to match `temp` type. Add `as nat` for integer division. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = ModExp_DivMod_helper(x_int, y_int, z_int);

    // Convert result_nat to a bit string (Vec<char>)
    let mut result_vec = Vec::<char>::new();
    let mut temp: nat = result_nat;
    if temp == (0 as nat) {
        result_vec.push('0');
    } else {
        while temp > (0 as nat)
            invariant
                temp % 2 == (0 as nat) || temp % 2 == (1 as nat),
                temp >= (0 as nat)
        {
            if temp % (2 as nat) == (1 as nat) {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            temp = (temp / (2 as nat)) as nat;
        }
    }
    result_vec.reverse(); // Reverse to get the correct order
    result_vec
}
// </vc-code>

fn main() {}
}

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
/* helper modified by LLM (iteration 5): no changes from previous iter. */
spec fn Power(x: nat, y: nat, z: nat) -> nat
    decreases y
{
    if y == 0 { 1nat % z } else if y == 1 { x % z } else if y % 2 == 0 { Power((x * x) % z, y / 2, z) } else { (x * Power((x * x) % z, y / 2, z)) % z }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): cast `result_int` to `nat` before assigning to `temp`. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = Power(x_int, y_int, z_int);

    let mut bit_string_vec: Vec<char> = Vec::new();
    let mut temp = result_nat as nat;
    if temp == 0 {
        bit_string_vec.push('0');
    } else {
        while temp > 0 {
            if temp % 2 == 1 {
                bit_string_vec.push('1');
            } else {
                bit_string_vec.push('0');
            }
            temp = temp / 2;
        }
    }
    bit_string_vec.reverse();
    bit_string_vec
}
// </vc-code>

fn main() {}
}

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
spec fn ModExp(x: nat, y: nat, z: nat) -> nat
{
    if y == 0 { 1 % z }
    else if y % 2 == 0 {
        let res = ModExp(x, y / 2, z);
        (res * res) % z
    }
    else {
        let res = ModExp(x, (y - 1) / 2, z);
        (x * res * res) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = ModExp(x_int, y_int, z_int);

    // Convert the natural number result back to a bit string (Vec<char>)
    // This is a simplified conversion; a full implementation for arbitrary `nat` to `Seq<char>` is complex
    // For now, we assume a direct conversion (which might not be straightforward for large numbers).
    // This part would typically involve a loop for base conversion.
    let mut result_vec = Vec::new();
    if result_nat == 0 {
        result_vec.push('0');
    } else {
        let mut temp_nat = result_nat;
        while temp_nat > 0 {
            if temp_nat % 2 == 1 {
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp_nat = temp_nat / 2;
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}

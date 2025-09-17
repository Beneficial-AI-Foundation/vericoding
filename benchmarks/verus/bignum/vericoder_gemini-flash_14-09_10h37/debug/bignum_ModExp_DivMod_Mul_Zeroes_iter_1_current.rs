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
spec fn ModExp(x: nat, y: nat, z: nat) -> nat {
    // Computes (x^y) % z
    // Requires z > 1
    if y == 0 {
        1 % z
    } else if y % 2 == 0 {
        let res = ModExp(x, y / 2, z);
        (res * res) % z
    } else {
        let res = ModExp(x, (y - 1) / 2, z);
        (x * ((res * res) % z)) % z
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
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    let result_nat = ModExp(x_val, y_val, z_val);

    // Convert the result_nat back to a bit string representation
    let mut result_vec = vec![];
    let mut temp = result_nat;

    if temp == 0 {
        result_vec.push('0');
    } else {
        while temp > 0 {
            if temp % 2 == 1 {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            temp = temp / 2;
        }
    }
    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}

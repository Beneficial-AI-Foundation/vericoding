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
/* helper modified by LLM (iteration 2): fixed type inference and mismatched type errors */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat
decreases y
{
    if y == 0 { 1nat % z }
    else if y % 2nat == 0 {
        let res = ModExp(x, y / 2nat, z);
        (res * res) % z
    }
    else {
        let res = ModExp(x, (y - 1nat) / 2nat, z);
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
/* code modified by LLM (iteration 2): fixed type mismatches */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = ModExp(x_int, y_int, z_int);

    let mut result_vec = Vec::new();
    if result_nat == 0nat {
        result_vec.push('0');
    } else {
        let mut temp_nat: nat = result_nat;
        while temp_nat > 0nat
          invariant
            result_vec.len() >= 0
        {
            if temp_nat % 2nat == 1nat {
                result_vec.insert(0, '1');
            } else {
                result_vec.insert(0, '0');
            }
            temp_nat = temp_nat / 2nat;
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}

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
spec fn ModExp_ModExpPow2_Zeroes_spec(sx: Seq<char>, sy: Seq<char>, sz: Seq<char>) -> nat {
    let sx_int = Str2Int(sx);
    let sy_int = Str2Int(sy);
    let sz_int = Str2Int(sz);
    Exp_int(sx_int, sy_int) % sz_int
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    if y_val == 0 {
        let mut res_vec = Vec::new();
        res_vec.push('1');
        return res_vec;
    }

    let half_y_val = y_val / 2;
    let sx_copy: Vec<char> = sx.to_vec();
    let sz_copy: Vec<char> = sz.to_vec();

    let half_y_str = nat_to_bitstring(half_y_val);

    let tmp_res_vec = ModExp_ModExpPow2_Zeroes(&sx_copy, &half_y_str, &sz_copy);
    let tmp_res_int = Str2Int(tmp_res_vec@);

    let final_int: nat;
    if y_val % 2 == 0 {
        final_int = (tmp_res_int * tmp_res_int) % z_val;
    } else {
        final_int = (x_val * tmp_res_int * tmp_res_int) % z_val;
    }

    let mut result_vec = Vec::new();
    let mut temp = final_int;
    if temp == 0 && z_val > 1{
      result_vec.push('0');
      return result_vec;
    }

    while temp > 0 {
        if temp % 2 == 0 {
            result_vec.push('0');
        } else {
            result_vec.push('1');
        }
        temp /= 2;
    }
    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}

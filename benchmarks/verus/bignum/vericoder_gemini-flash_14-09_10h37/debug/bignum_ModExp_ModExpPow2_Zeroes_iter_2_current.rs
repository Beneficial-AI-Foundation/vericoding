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
/* helper modified by LLM (iteration 2): Added helper function `nat_to_bitstring` */
spec fn nat_to_bitstring(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::new(
        &['0']
    ) } else if n == 1 { Seq::new(
        &['1']
    ) } else {
        let last_bit = if n % 2 == 0 { '0' } else { '1' };
        nat_to_bitstring(n / 2).snoc(last_bit)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Added implementation for recursive calls */
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
    let half_y_str_seq = nat_to_bitstring(half_y_val);
    let half_y_str_vec: Vec<char> = half_y_str_seq.to_vec();

    let sub_problem_res_vec = ModExp_ModExpPow2_Zeroes(sx, &half_y_str_vec, sz);
    let tmp_res_int = Str2Int(sub_problem_res_vec@);

    let final_int: nat;
    if y_val % 2 == 0 {
        final_int = (tmp_res_int * tmp_res_int) % z_val;
    } else {
        final_int = (x_val * tmp_res_int * tmp_res_int) % z_val;
    }

    let mut result_vec = Vec::new();
    let mut temp = final_int;
    if temp == 0 && z_val > 1 {
      result_vec.push('0');
      return result_vec;
    }

    if temp == 0 {
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

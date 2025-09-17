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
/* helper modified by LLM (iteration 3): No change needed. */
spec fn num_to_bit_string(n: nat) -> Seq<char>
decreases n
{
    if n == 0 { Seq::singleton('0') }
    else {
        let rem: nat = n % 2;
        let div: nat = n / 2;
        if div == 0 { 
            if rem == 0 { Seq::singleton('0') } else { Seq::singleton('1') }
        } else {
            let mut res = num_to_bit_string(div);
            res = res.push(if rem == 0 { '0' } else { '1' });
            res
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Cast to `nat` and `int` for `num_to_bit_string` arguments within ghost context. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if y_int == 0 {
        if z_int == 1 {
            return vec!['0'];
        } else {
            return vec!['1'];
        }
    }

    let mut result_nat: nat;
    if y_int % 2 == 1 {
        let sub_exp = ModExp_DivMod_ModExpPow2_Zeroes(sx, &num_to_bit_string((y_int - 1) as nat).to_vec(), sz);
        result_nat = (x_int * Str2Int(sub_exp@)) % z_int;
    } else {
        let sub_exp_half = ModExp_DivMod_ModExpPow2_Zeroes(sx, &num_to_bit_string((y_int / 2) as nat).to_vec(), sz);
        let sub_exp_half_int = Str2Int(sub_exp_half@);
        result_nat = (sub_exp_half_int * sub_exp_half_int) % z_int;
    }

    num_to_bit_string(result_nat).to_vec()
}
// </vc-code>

fn main() {}
}

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
/* helper modified by LLM (iteration 4): Removed unnecessary helper */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Converted `Str2Int` to `nat` where needed, and explicitly cast results of `Str2Int` to `nat` where they were used with mathematical operations that expect `nat`. */
{
    if Str2Int(sy@) == 0 {
        let mut vec_res = Vec::<char>::new();
        vec_res.push('1');
        vec_res
    } else if Str2Int(sy@) == 1 {
        let mut res_vec = Vec::<char>::new();
        for i in 0..sx.len() {
            res_vec.push(sx[i]);
        }
        res_vec
    } else if (Str2Int(sy@) % 2) == 0 {
        // Even exponent
        let mut half_sy_vec: Vec<char> = Vec::new();
        let half_sy_int: nat = (Str2Int(sy@) / 2) as nat;
        if half_sy_int == 0 {
            half_sy_vec.push('0');
        } else {
            let mut temp_half_sy_int: nat = half_sy_int;
            while temp_half_sy_int > 0
                invariant
                    temp_half_sy_int >= 0,
            {
                if (temp_half_sy_int % 2) == 1 {
                    half_sy_vec.insert(0, '1');
                } else {
                    half_sy_vec.insert(0, '0');
                }
                temp_half_sy_int = (temp_half_sy_int / 2) as nat;
            }
        }

        let result_half = ModExp_DivMod_Mul_Zeroes(sx, &half_sy_vec.view_as_slice(), sz);
        let mut result_vec = Vec::<char>::new();
        let result_int: nat = (Str2Int(result_half@) * Str2Int(result_half@)) % Str2Int(sz@);
        if result_int == 0 {
            result_vec.push('0');
        } else {
            let mut temp_result_int: nat = result_int;
            while temp_result_int > 0
                invariant
                    temp_result_int >= 0,
            {
                if (temp_result_int % 2) == 1 {
                    result_vec.insert(0, '1');
                } else {
                    result_vec.insert(0, '0');
                }
                temp_result_int = (temp_result_int / 2) as nat;
            }
        }
        result_vec
    } else {
        // Odd exponent
        let mut sy_minus_1_vec: Vec<char> = Vec::new();
        let sy_minus_1_int: nat = (Str2Int(sy@) - 1) as nat;
        if sy_minus_1_int == 0 {
            sy_minus_1_vec.push('0');
        } else {
            let mut temp_sy_minus_1_int: nat = sy_minus_1_int;
            while temp_sy_minus_1_int > 0
                invariant
                    temp_sy_minus_1_int >= 0,
            {
                if (temp_sy_minus_1_int % 2) == 1 {
                    sy_minus_1_vec.insert(0, '1');
                } else {
                    sy_minus_1_vec.insert(0, '0');
                }
                temp_sy_minus_1_int = (temp_sy_minus_1_int / 2) as nat;
            }
        }

        let result_sy_minus_1 = ModExp_DivMod_Mul_Zeroes(sx, &sy_minus_1_vec.view_as_slice(), sz);
        let mut result_vec = Vec::<char>::new();
        let result_int: nat = (Str2Int(sx@) * Str2Int(result_sy_minus_1@)) % Str2Int(sz@);
        if result_int == 0 {
            result_vec.push('0');
        } else {
            let mut temp_result_int: nat = result_int;
            while temp_result_int > 0
                invariant
                    temp_result_int >= 0,
            {
                if (temp_result_int % 2) == 1 {
                    result_vec.insert(0, '1');
                } else {
                    result_vec.insert(0, '0');
                }
                temp_result_int = (temp_result_int / 2) as nat;
            }
        }
        result_vec
    }
}
// </vc-code>

fn main() {}
}

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
/* helper modified by LLM (iteration 6): Used `vstd::builtin::pow2` to avoid `log_2_bound` on int and made `temp_val` a ghost variable instead of `nat` */
fn nat_to_vec_char(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    let mut ghost temp_val = n;

    if n == 0 {
        result.push('0');
        return result;
    }

    while temp_val > 0
        invariant
            temp_val >= 0,
            ValidBitString(result@),
            Str2Int(result@) + vstd::builtin::pow2(result.len() as nat) * temp_val == n
        decreases temp_val
    {
        if temp_val % 2 == 1 {
            result.insert(0, '1');
        } else {
            result.insert(0, '0');
        }
        temp_val = (temp_val / 2) as nat;
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Cast `sy.len()` to `usize` for indexing and corrected `int` to `nat` for `half_y_seq` length to avoid compilation error */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    if y == 0 {
        let mut res = Vec::<char>::new();
        res.push('1');
        return res;
    } else if sy.len() == 1 && sy[0] == '1' {
        let val = x % z;
        return nat_to_vec_char(val);
    } else {

        let (half_y_seq, half_y_vec) = if sy[sy.len() as usize - 1] == '0' {
            let half_y_seq = sy@.subrange(0, (sy.len()) as nat - 1);
            let half_y_vec = seq_to_vec_char(half_y_seq);
            (half_y_seq, half_y_vec)
        } else {
            let half_y_seq = sub_one(sy@);
            let half_y_vec = seq_to_vec_char(half_y_seq);
            (half_y_seq, half_y_vec)
        };

        let half_y_str = &half_y_vec;
        let half_y_int = Str2Int(half_y_str@);
        let res_half_vec = ModExp_DivMod_ModExpPow2(sx, half_y_str, sz);
        let res_half_int = Str2Int(res_half_vec@);

        if sy[sy.len() as usize - 1] == '0' {
            let final_res_int = (res_half_int * res_half_int) % z;
            return nat_to_vec_char(final_res_int);
        } else {
            let final_res_int = (x * res_half_int * res_half_int) % z ;
            return nat_to_vec_char(final_res_int);
        }
    }
}
// </vc-code>

fn main() {}
}

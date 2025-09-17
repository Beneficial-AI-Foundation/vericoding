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
/* helper modified by LLM (iteration 3): Removed unused lemma, it's not needed for the current verification error. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation error by changing `temp_sy_vec@[i as int]` to `temp_sy_vec[i]` because `i` is already `usize` and `temp_sy_vec` is a `Vec<char>`. This allows direct indexing. */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);

    if y == 0 {
        let mut res = Vec::<char>::new();
        res.push('1');
        return res;
    } else if sy.len() == 1 && sy@[0] == '1' {
        let mut res = Vec::<char>::new();
        let val = x % z;
        let mut temp_val = val;
        if temp_val == 0 {
            res.push('0');
        } else {
            while temp_val > 0
                invariant
                    temp_val >= 0,
                    ValidBitString(res@),
                decreases temp_val
            {
                if temp_val % 2 == 1 {
                    res.insert(0, '1');
                } else {
                    res.insert(0, '0');
                }
                temp_val = temp_val / 2;
            }
        }
        return res;
    } else {
        let half_y_str = if sy@[sy.len() - 1] == '0' {
            sy.subslice(0, sy.len() - 1)
        } else {
            let mut temp_sy_vec = Vec::<char>::from_seq(sy@);
            let mut carry = true;
            let mut i: usize = sy.len() - 1;
            while i >= 0 && carry
                invariant
                    0 <= i,
                    carry == (forall |j: int| i < j && j < sy.len() ==> temp_sy_vec@[j as int] == '0' ),
                    temp_sy_vec.len() == sy.len(),
                    ValidBitString(temp_sy_vec@),
                    ValidBitString(sy@),
                decreases i
            {
                if temp_sy_vec[i] == '1' {
                    temp_sy_vec.to_bytes()[i] = '0' as u8;
                } else {
                    temp_sy_vec.to_bytes()[i] = '1' as u8;
                    carry = false;
                }
                if i == 0 { break; }
                i = i - 1;
            }
            temp_sy_vec.subslice(0, sy.len() - 1)
        };

        let half_y = Str2Int(half_y_str@);
        let mut res_half = ModExp_DivMod_ModExpPow2(sx, &half_y_str, sz);
        let res_half_int = Str2Int(res_half@);

        if sy@[sy.len() - 1] == '0' {
            let final_res_int = (res_half_int * res_half_int) % z;
            let mut res_chars = Vec::<char>::new();
            let mut temp_val = final_res_int;
            if temp_val == 0 {
                res_chars.push('0');
            } else {
                while temp_val > 0
                    invariant
                        temp_val >= 0,
                        ValidBitString(res_chars@),
                    decreases temp_val
                {
                    if temp_val % 2 == 1 {
                        res_chars.insert(0, '1');
                    }
                    else {
                        res_chars.insert(0, '0');
                    }
                    temp_val = temp_val / 2;
                }
            }
            return res_chars;
        } else {
            let final_res_int = (x * res_half_int % z * res_half_int % z) % z;
            let mut res_chars = Vec::<char>::new();
            let mut temp_val = final_res_int;
            if temp_val == 0 {
                res_chars.push('0');
            } else {
                while temp_val > 0
                    invariant
                        temp_val >= 0,
                        ValidBitString(res_chars@),
                    decreases temp_val
                {
                    if temp_val % 2 == 1 {
                        res_chars.insert(0, '1');
                    } else {
                        res_chars.insert(0, '0');
                    }
                    temp_val = temp_val / 2;
                }
            }
            return res_chars;
        }
    }
}
// </vc-code>

fn main() {}
}

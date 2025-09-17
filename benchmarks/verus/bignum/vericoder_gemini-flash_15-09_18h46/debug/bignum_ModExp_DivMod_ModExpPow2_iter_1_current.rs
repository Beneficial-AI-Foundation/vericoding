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
proof fn lemma_div_mod_auto(a: nat, b: nat) ensures a % b < b { }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
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
            let mut temp_sy = Vec::<char>::from_seq(sy@);
            let mut carry = true;
            let mut i = sy.len() as int - 1;
            while i >= 0 && carry
                invariant
                    0 <= i,
                    carry == (forall |j: int| i < j && j < sy.len() ==> temp_sy@[j] == '0'),
                    temp_sy.len() == sy.len(),
                    ValidBitString(temp_sy@),
                    ValidBitString(sy@),
                decreases i
            {
                if temp_sy@[i] == '1' {
                    temp_sy.to_bytes()[i as usize] = '0' as u8;
                } else {
                    temp_sy.to_bytes()[i as usize] = '1' as u8;
                    carry = false;
                }
                i = i - 1;
            }
            temp_sy.subslice(0, sy.len() - 1)
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
                    } else {
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

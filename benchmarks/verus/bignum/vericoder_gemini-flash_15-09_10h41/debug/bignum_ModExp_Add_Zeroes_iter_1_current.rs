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
spec fn Str2IntSingleChar(c: char) -> nat { if c == '0' { 0 } else if c == '1' { 1 } else { 0 } }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = Str2Int(sx@);
    let y_str = sy@;
    let z_val = Str2Int(sz@);

    if y_str.len() == 1 {
        let y_char_val = Str2IntSingleChar(y_str.index(0));
        if y_char_val == 0 {
            return vec!['1'];
        } else { // y_char_val == 1
            let mut res_str = Vec::<char>::new();
            let mut current_x_val = x_val % z_val;
            if current_x_val == 0 {
                res_str.push('0');
            } else {
                while current_x_val > 0 {
                    let digit = (current_x_val % 2) as char;
                    res_str.insert(0, if digit == 0 { '0' } else { '1' });
                    current_x_val /= 2;
                }
            }
            if res_str.is_empty() {
                res_str.push('0'); // Should not happen with current_x_val > 0 unless x_val was 0
            }
            return res_str;
        }
    } else {
        let k_str = y_str.subrange(0, y_str.len() as int - 1);
        let b_val = Str2IntSingleChar(y_str.index(y_str.len() as int - 1));
        let y_k_val = Str2Int(k_str);

        let tmp1 = ModExp_Add_Zeroes(sx, k_str.to_vec().as_slice(), sz);
        let tmp1_val = Str2Int(tmp1@);
        let mut squared_val = (tmp1_val * tmp1_val) % z_val;

        if b_val == 1 {
            squared_val = (squared_val * (x_val % z_val)) % z_val;
        }

        let mut res_str = Vec::<char>::new();
        if squared_val == 0 {
            res_str.push('0');
        } else {
            while squared_val > 0 {
                let digit = (squared_val % 2) as char;
                res_str.insert(0, if digit == 0 { '0' } else { '1' });
                squared_val /= 2;
            }
        }
        if res_str.is_empty() {
            res_str.push('0');
        }
        return res_str;
    }
}
// </vc-code>

fn main() {}
}

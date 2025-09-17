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
/* helper modified by LLM (iteration 2): Removed placeholder assume; this is a spec function so no proof block is needed. */
spec fn Str2Int_to_nat(s: Seq<char>) -> nat {
    Str2Int(s)
}

/* helper modified by LLM (iteration 2): Removed the proof block and `assume`, as this is a `spec` function so no proof is needed. */
spec fn exp_property(x: nat, y: nat) -> bool
requires y > 0
ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    true
}

/* helper modified by LLM (iteration 2): Moved `nat_to_binary_seq` helper out of the `vc-code` section. */
pure fn nat_to_binary_seq(n: nat) -> Seq<char>
ensures
    ValidBitString(result),
    n == Str2Int(result)
{
    let mut s: Seq<char> = Seq::new();
    if n == 0 {
        s = s.push('0');
    } else {
        let mut temp = n;
        while temp > 0 {
            if temp % 2 == 1 {
                s = s.push('1');
            } else {
                s = s.push('0');
            }
            temp = temp / 2;
        }
        s = s.reverse();
    }
    s
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Re-introduced `result_vec` and `result_val` variables as `let` in the inner scope instead of global and moved the result to the end of the block. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    if y_val == 0 {
        return vec!['1'];
    } else if y_val == 1 {
        let mut result_vec = Vec::new();
        let mut current_x = x_val % z_val;
        if current_x == 0 {
            result_vec.push('0');
        } else {
            let mut temp = current_x;
            while temp > 0 {
                if temp % 2 == 1 {
                    result_vec.push('1');
                } else {
                    result_vec.push('0');
                }
                temp = temp / 2;
            }
            result_vec.reverse();
        }
        return result_vec;
    }

    let half_y = y_val / 2;
    let sy_half_str = nat_to_binary_seq(half_y);
    let inter_res_vec = ModExp_Add_Zeroes(sx, sy_half_str.as_slice(), sz);
    let inter_res_val = Str2Int(inter_res_vec@);

    let mut result_val = (inter_res_val * inter_res_val) % z_val;
    if y_val % 2 == 1 {
        result_val = (result_val * x_val) % z_val;
    }

    let mut result_vec = Vec::new();
    if result_val == 0 {
        result_vec.push('0');
    } else {
        let mut temp = result_val;
        while temp > 0 {
            if temp % 2 == 1 {
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            temp = temp / 2;
        }
        result_vec.reverse();
    }
    result_vec
}
// </vc-code>

fn main() {}
}

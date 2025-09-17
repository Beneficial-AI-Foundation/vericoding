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
/* helper modified by LLM (iteration 5): Corrected `nat_to_binary_seq` function by removing unnecessary `Str2Int_to_nat` helper and fixing compilation error within `nat_to_binary_seq` where `ValidBitString(s)` was misplaced. */
spec fn nat_to_binary_seq(n: nat) -> (s_out: Seq<char>)
ensures
    n == Str2Int(s_out),
    ValidBitString(s_out)
decreases n
{
    if n == 0 {
        assert(ValidBitString(Seq::singleton('0')));
        Seq::singleton('0')
    } else {
        let mut s: Seq<char> = Seq::new();
        let mut temp = n;
        while temp > 0
            invariant
                ValidBitString(s),
                n >= temp,
                temp >= 0,
                // This invariant assumes Str2Int(nat_to_binary_seq(temp)) * Exp_int(2, s.len() as nat) is the 'remaining' part
                // For a more precise invariant, we'd need to formalize the relation between n, temp, and s
            {
            if temp % 2 == 1 {
                s = s.push('1');
            } else {
                s = s.push('0');
            }
            temp = temp / 2;
        }
        s.reverse()
    }
}

spec fn exp_property(x: nat, y: nat) -> bool
requires y > 0
ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    true
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error in `ModExp_Add_Zeroes` by ensuring `ValidBitString` for the result sequence returned by `nat_to_binary_seq`. Also, addressed the misplaced `if-else` statement to ensure all paths return a `Vec<char>`. */
{
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);

    if y_val == 0 {
        let s = Seq::singleton('1');
        proof {
            assert(ValidBitString(s));
            assert(Str2Int(s) == 1nat);
        }
        let mut result_vec = Vec::new();
        result_vec.push('1');
        result_vec
    } else if y_val == 1 {
        let current_x = x_val % z_val;
        let s = nat_to_binary_seq(current_x);
        proof { assert(ValidBitString(s)); }
        let mut result_vec = Vec::new();
        let mut i = 0;
        while i < s.len() {
            result_vec.push(s.index(i));
            i = i + 1;
        }
        result_vec
    } else {
        let half_y = y_val / 2;
        let sy_half_str: Seq<char> = nat_to_binary_seq(half_y);

        let mut inter_res_vec_char = Vec::new();
        let mut i = 0;
        while i < sy_half_str.len() {
            inter_res_vec_char.push(sy_half_str.index(i));
            i = i + 1;
        }

        let inter_res_vec = ModExp_Add_Zeroes(sx, inter_res_vec_char.as_slice(), sz);
        let inter_res_val = Str2Int(inter_res_vec@);

        let mut result_val = (inter_res_val * inter_res_val) % z_val;
        if y_val % 2 == 1 {
            result_val = (result_val * x_val) % z_val;
        }

        let s = nat_to_binary_seq(result_val);
        proof { assert(ValidBitString(s)); }
        let mut result_vec = Vec::new();
        let mut i = 0;
        while i < s.len() {
            result_vec.push(s.index(i));
            i = i + 1;
        }
        result_vec
    }
}
// </vc-code>

fn main() {}
}

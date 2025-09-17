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
/* helper modified by LLM (iteration 3): Removed extraneous `as nat` casts; they are unnecessary when both operands are `nat`. */
spec fn Exp_int_mod(x: nat, y: nat, m: nat) -> nat
decreases y
{
    if y == 0 { 1 % m }
    else if y == 1 { x % m }
    else {
        let half_y = y / 2;
        let half_res = Exp_int_mod(x, half_y, m);
        if y % 2 == 0 {
            (half_res * half_res) % m
        } else {
            (x * half_res * half_res) % m
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Removed `as nat` casts for `temp_val` assignments, as `temp_val` is already `nat`. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_val = Exp_int_mod(x_int, y_int, z_int);

    // Convert result_val (nat) back to a binary string (Vec<char>)
    let mut binary_string_vec = Vec::<char>::new();
    let mut temp_val: nat = result_val;

    if temp_val == 0 {
        binary_string_vec.push('0');
    } else {
        while (temp_val > 0)
            invariant
                temp_val >= 0,
                forall |i: int| #![auto] 0 <= i && i < binary_string_vec@.len() ==> (binary_string_vec@[i] == '0' || binary_string_vec@[i] == '1'),
            decreases temp_val
        {
            let digit = if (temp_val % 2) == 1 { '1' } else { '0' };
            binary_string_vec.push(digit);
            temp_val = temp_val / 2;
        }
        binary_string_vec.reverse();
    }

    binary_string_vec
}
// </vc-code>

fn main() {}
}

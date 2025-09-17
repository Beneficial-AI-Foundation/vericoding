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
/* helper modified by LLM (iteration 4): Removed `nat` casting within `seq_to_vec_char` */
exec fn seq_to_vec_char(s: Seq<char>) -> Vec<char>
{
    let mut vec_char = Vec::<char>::new();
    let mut i: int = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            vec_char@.len() == i,
            forall |j: int| 0 <= j && j < i ==> vec_char@[j] == s.index(j)
    {
        vec_char.push(s.index(i));
        i = i + 1;
    }
    vec_char
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Corrected `nat` and `int` type casting errors. */
{
    let x_int = Str2Int(sx@);
    let y_int_spec = Str2Int(sy@);
    let z_int_spec = Str2Int(sz@);

    if y_int_spec == 0 {
        let res_int = 1 % z_int_spec;
        let res_str_seq = int_to_bit_string(res_int);
        
        return seq_to_vec_char(res_str_seq);
    } else if y_int_spec == 1 {
        let res_int = x_int % z_int_spec;
        let res_str_seq = int_to_bit_string(res_int);

        return seq_to_vec_char(res_str_seq);
    } else {
        let y_half_seq = divide_by_2_string(y_int_spec).get_Some_0();
        let y_half_vec = seq_to_vec_char(y_half_seq);

        let recurse_result = ModExp_int(sx, &y_half_vec, sz);
        let recurse_result_int = Str2Int(recurse_result@);

        let mut res_int: nat;
        if y_int_spec % 2 == 0 {
            res_int = (recurse_result_int * recurse_result_int) % z_int_spec;
        } else {
            res_int = (x_int * recurse_result_int * recurse_result_int) % z_int_spec;
        }
        
        let res_str_seq = int_to_bit_string(res_int);

        return seq_to_vec_char(res_str_seq);
    }
}
// </vc-code>

fn main() {}
}

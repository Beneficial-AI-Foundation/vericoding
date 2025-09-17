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
proof fn bit_string_to_nat_is_valid() {} 
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if sy@.len() == 0 {
        let res_int = Exp_int(x_int, y_int) % z_int;
        let res_str_seq = int_to_bit_string(res_int);
        let mut vec_char = Vec::<char>::new();
        let mut i = 0;
        while i < res_str_seq.len() as int
            invariant
                0 <= i <= res_str_seq.len() as int,
                vec_char@.len() == i,
                forall |j: int| 0 <= j && j < i ==> vec_char@[j] == res_str_seq.index(j)
            decreases res_str_seq.len() as int - i
        {
            vec_char.push(res_str_seq.index(i));
            i = i + 1;
        }
        return vec_char;
    } else if y_int == 0 {
        let res_int = 1 % z_int;
        let res_str_seq = int_to_bit_string(res_int);
        let mut vec_char = Vec::<char>::new();
        let mut i = 0;
        while i < res_str_seq.len() as int
            invariant
                0 <= i <= res_str_seq.len() as int,
                vec_char@.len() == i,
                forall |j: int| 0 <= j && j < i ==> vec_char@[j] == res_str_seq.index(j)
            decreases res_str_seq.len() as int - i
        {
            vec_char.push(res_str_seq.index(i));
            i = i + 1;
        }
        return vec_char;
    } else {
        let y_minus_1_seq = divide_by_2_string(y_int).get_Some_0();
        let recurse_result = ModExp_int(sx, &seq_to_vec_char(y_minus_1_seq["s"]["val"]), sz);
        let recurse_result_int = Str2Int(recurse_result@);

        let mut res_int: nat;
        if y_int % 2 == 0 {
            res_int = (recurse_result_int * recurse_result_int) % z_int;
        } else {
            res_int = (x_int * recurse_result_int * recurse_result_int) % z_int;
        }
        
        let res_str_seq = int_to_bit_string(res_int);
        let mut vec_char = Vec::<char>::new();
        let mut i = 0;
        while i < res_str_seq.len() as int
            invariant
                0 <= i <= res_str_seq.len() as int,
                vec_char@.len() == i,
                forall |j: int| 0 <= j && j < i ==> vec_char@[j] == res_str_seq.index(j)
            decreases res_str_seq.len() as int - i
        {
            vec_char.push(res_str_seq.index(i));
            i = i + 1;
        }
        return vec_char;
    }
}
// </vc-code>

fn main() {}
}

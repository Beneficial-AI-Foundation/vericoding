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
/* helper modified by LLM (iteration 5): Added a helper function to convert nat to Seq<char>. */
spec fn int_to_bit_string_spec(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n == 1 {
        seq!['1']
    } else {
        let last_bit = if n % 2 == 1 { '1' } else { '0' };
        int_to_bit_string_spec(n / 2).push(last_bit)
    }
}

fn char_to_int(c: char) -> (i: nat) ensures (c == '0' ==> i == 0) && (c == '1' ==> i == 1) { c as nat - '0' as nat }

fn int_to_char(i: nat) -> (c: char) ensures (i == 0 ==> c == '0') && (i == 1 ==> c == '1') { (i + '0' as nat) as char }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Used ghost variable y_int for calculations and int_to_bit_string_spec for conversion. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if y_int == 0 {
        let res_nat = 1 % z_int;
        return int_to_bit_string_spec(res_nat).into_vec();
    }

    let mut result_vec: Vec<char>;
    if y_int == 1 {
        let res_nat = x_int % z_int;
        return int_to_bit_string_spec(res_nat).into_vec();
    } else if (y_int % 2) == 0 {
        // y is even
        let y_half = y_int / 2;
        let half_exp_res = ModExp_DivMod(sx, int_to_bit_string_spec(y_half).as_slice(), sz);
        let half_exp_res_int = Str2Int(half_exp_res@);
        let res_nat = (half_exp_res_int * half_exp_res_int) % z_int;
        return int_to_bit_string_spec(res_nat).into_vec();
    } else {
        // y is odd
        let y_minus_1 = (y_int - 1);
        let y_minus_1_exp_res = ModExp_DivMod(sx, int_to_bit_string_spec(y_minus_1).as_slice(), sz);
        let y_minus_1_exp_res_int = Str2Int(y_minus_1_exp_res@);
        let res_nat = (x_int * y_minus_1_exp_res_int) % z_int;
        return int_to_bit_string_spec(res_nat).into_vec();
    }
}
// </vc-code>

fn main() {}
}

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
spec fn ModExp_DivMod_spec(x: nat, y: nat, z: nat) -> nat {
    Exp_int(x, y) % z
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if sy@.len() == 1 && sy@[0] == '0' {
        // y is 0, x^0 mod z = 1 mod z
        if z_int > 1 {
            return Util::int_to_str(1 % z_int);
        } else {
             // This case is excluded by the preconditions (z_int > 1)
             panic("z_int must be greater than 1");
        }
    }

    let mut result_vec: Vec<char>;
    if y_int == 0 {
        result_vec = Util::int_to_str(1 % z_int);
    } else if y_int == 1 {
        result_vec = Util::int_to_str(x_int % z_int);
    } else if y_int % 2 == 0 {
        // y is even
        let y_half = y_int / 2;
        let half_exp_str = ModExp_DivMod(sx, Util::int_to_str(y_half).as_slice(), sz);
        let half_exp_int = Str2Int(half_exp_str@);
        let square_val = (half_exp_int * half_exp_int) % z_int;
        result_vec = Util::int_to_str(square_val);
    } else {
        // y is odd
        let y_minus_1 = y_int - 1;
        let term1_str = ModExp_DivMod(sx, Util::int_to_str(y_minus_1).as_slice(), sz);
        let term1_int = Str2Int(term1_str@);
        let term2_int = x_int % z_int;
        let product_val = (term1_int * term2_int) % z_int;
        result_vec = Util::int_to_str(product_val);
    }

    result_vec
}
// </vc-code>

fn main() {}
}

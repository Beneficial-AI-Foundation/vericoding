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
/* helper modified by LLM (iteration 2): The spec function `ModExp_DivMod_Mul_spec` is correctly defined as `Exp_int(x, y) % z`. No logical changes required. */
spec fn ModExp_DivMod_Mul_spec(x: nat, y: nat, z: nat) -> nat {
    Exp_int(x, y) % z
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
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
        let mut vec = Vec::new();
        vec.push('1');
        return vec;
    }

    let mut res_nat = 1_nat;
    let mut base = x_int % z_int;
    let mut exp = y_int;

    while exp > 0 {
        /* invariant res_nat % z_int == (Exp_int(x_int, y_int) % z_int * (Exp_int(base, exp) % z_int).inverse(z_int)) % z_int, */
        /* The above invariant is too complex and attempts to use `inverse` which is not available for `nat` due to potential division by zero etc. */
        /* A simpler invariant is that the product of `res_nat` and `base^exp` modulo `z_int` remains consistent with the initial `x_int^y_int` modulo `z_int`. */
        /* It's more robust to work with the `ModExp_DivMod_Mul_spec` directly. */
        invariant 0 <= exp,
        invariant (res_nat * Exp_int(base, exp)) % z_int == ModExp_DivMod_Mul_spec(x_int, y_int, z_int),
        decreases exp

        if exp % 2 == 1 {
            res_nat = (res_nat * base) % z_int;
        }
        base = (base * base) % z_int;
        exp = exp / 2;
    }

    let mut result_vec = Vec::new();
    if res_nat == 0 {
        result_vec.push('0');
        return result_vec;
    }

    let mut temp_nat = res_nat;
    while temp_nat > 0 {
        invariant temp_nat >= 0,
        decreases temp_nat
        if temp_nat % 2 == 1 {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp_nat = temp_nat / 2;
    }

    result_vec
}
// </vc-code>

fn main() {}
}

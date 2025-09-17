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
spec fn ModPow(base: nat, exp: nat, modulus: nat) -> nat
    decreases exp
{
    if exp == 0 {
        1
    } else if exp % 2 == 0 {
        let half_exp = ModPow(base, exp / 2, modulus);
        (half_exp * half_exp) % modulus
    } else {
        (base * ModPow(base, (exp - 1) as nat, modulus)) % modulus
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed `nat` literals in `while` loop conditions by casting them to `nat` type. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_int = ModPow(x_int, y_int, z_int);

    let mut result_vec = Vec::<char>::new();
    let mut temp_val: nat = result_int;
    while temp_val > 0nat
        invariant
            temp_val >= 0nat,
    {
        if temp_val % 2nat == 1nat {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp_val = temp_val / 2nat;
    }

    if result_vec.len() == 0 {
        result_vec.push('0'); // Handle the case where result_int is 0
    }

    result_vec
}
// </vc-code>

fn main() {}
}

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
spec fn mul_mod_spec(a: nat, b: nat, m: nat) -> nat { (a * b) % m }
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if y_int == 0 {
        return int_to_bitstring(1, z_int);
    } else {
        let k = y_int / 2;
        let r = y_int % 2;

        let sx_copy: Vec<char> = sx.to_vec();
        let sy_k_vec = int_to_bitstring(k, z_int); // Dummy length needed for new_function_here_ModExp_Add_ModExpPow2_Zeroes
        let sz_copy: Vec<char> = sz.to_vec();

        let res_k = new_function_here_ModExp_Add_ModExpPow2_Zeroes(&sx_copy, &sy_k_vec, &sz_copy);

        let sq_res_k_int = mul_mod_spec(Str2Int(res_k@), Str2Int(res_k@), z_int);

        if r == 1 {
            let final_res_int = mul_mod_spec(sq_res_k_int, x_int, z_int);
            return int_to_bitstring(final_res_int, z_int);
        } else {
            return int_to_bitstring(sq_res_k_int, z_int);
        }
    }
}
// </vc-code>

fn main() {}
}

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
/* helper modified by LLM (iteration 10): Removed. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Declare ghost variable for nat operations. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let ghost_result_nat = Exp_int(x_int, y_int) % z_int;

    // Convert result_nat back to a bit string
    let mut bit_string_rev: Vec<char> = Vec::new();
    let mut ghost temp_nat = ghost_result_nat;

    if ghost temp_nat == 0 {
        bit_string_rev.push('0');
    }

    while ghost temp_nat > 0
        invariant
            ghost temp_nat >= 0,
        decreases ghost temp_nat
    {
        if ghost temp_nat % 2 == 1 {
            bit_string_rev.push('1');
        } else {
            bit_string_rev.push('0');
        }
        ghost temp_nat = ghost temp_nat / 2;
    }

    let mut res: Vec<char> = Vec::new();
    let mut i = bit_string_rev.len();
    while i > 0
        invariant
            i <= bit_string_rev.len(),
        decreases i
    {
        i = i - 1;
        res.push(*bit_string_rev.get(i).unwrap());
    }
    res
}
// </vc-code>

fn main() {}
}

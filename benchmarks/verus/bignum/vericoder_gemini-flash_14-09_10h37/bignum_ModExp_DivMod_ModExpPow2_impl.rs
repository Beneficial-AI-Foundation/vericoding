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

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatch errors by ensuring all numeric literals and operations on `nat` types are correctly handled as `nat`. Specifically, replaced `1nat` with `1` and ensured `temp / 2` remains a `nat` by leveraging automatic type inference where possible or explicitly casting back to `nat` if needed for division. Corrected `temp == 0` for `nat` comparison. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_int = Exp_int(x_int, y_int) % z_int;

    let mut result_vec = Vec::new();
    let mut temp: nat = result_int;

    if temp == 0 {
        result_vec.push('0');
        return result_vec;
    }

    while temp > 0 {
        if temp % 2 == 1 {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp = (temp / 2) as nat;
    }
    result_vec
}
// </vc-code>

fn main() {}
}

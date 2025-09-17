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
/* helper modified by LLM (iteration 4): Removed the now unused `ModExp_DivMod_power_base` helper. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Changed `temp = (temp / 2) as nat;` to `temp = temp / 2;` to avoid `as nat` cast issues. The `temp` variable is already typed as `nat`, so the cast is redundant and causes errors when `temp / 2` is implicitly `int`. */
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
        if temp % 2 == 1nat {
            result_vec.insert(0, '1');
        } else {
            result_vec.insert(0, '0');
        }
        temp = temp / 2;
    }
    result_vec
}
// </vc-code>

fn main() {}
}

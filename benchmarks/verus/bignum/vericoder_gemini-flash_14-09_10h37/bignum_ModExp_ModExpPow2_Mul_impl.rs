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
/* helper modified by LLM (iteration 5): No changes needed in helper, compilation errors were in the main code. */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat {
    if y == 0 {
        1nat % z
    } else if y % 2 == 0 {
        let res = ModExp(x, y / 2, z);
        (res * res) % z
    } else {
        (x * ModExp(x, (y - 1) as nat, z)) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed invalid `nat` suffix from integer literals. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_nat = ModExp(x_int, y_int, z_int);

    let mut digits: Vec<char> = Vec::new();
    if result_nat == 0 { // Removed 'nat' suffix
        digits.push('0');
    } else {
        let mut temp: nat = result_nat;
        while temp > 0
            invariant
                temp >= 0nat // This is fine
        {
            if temp % 2 == 1 { // Removed 'nat' suffix
                digits.push('1');
            } else {
                digits.push('0');
            }
            temp = temp / 2;
        }
    }
    digits.reverse();

    digits
}
// </vc-code>

fn main() {}
}

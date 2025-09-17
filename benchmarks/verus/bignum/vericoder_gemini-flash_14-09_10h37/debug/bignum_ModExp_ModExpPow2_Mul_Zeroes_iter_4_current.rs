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
/* helper modified by LLM (iteration 4): The modulo operation should be applied carefully for each step of the modular exponentiation. */
spec fn ModExp_ModExpPow2_Mul(x: nat, y: nat, z: nat) -> nat
decreases y
{
    if y == 0 { 1 } else if y % 2 == (0 as nat) { ModExp_ModExpPow2_Mul(x * x % z, y / (2 as nat), z) } else { x * (ModExp_ModExpPow2_Mul(x * x % z, y / (2 as nat), z)) % z }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): The issue indicates a type mismatch between `nat` and `integer` in `result_nat == 0`, `while temp_nat > 0`, `if temp_nat % 2 == 1` and `temp_nat = temp_nat / 2` expressions. Explicitly casting the integer literals `0`, `1`, and `2` to `nat` using `as nat` should resolve these errors. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);
    let result_nat = ModExp_ModExpPow2_Mul(x_int, y_int, z_int);

    // Convert result_nat back to a bit string
    let mut bit_string: Vec<char> = Vec::new();
    if result_nat == (0 as nat) {
        bit_string.push('0');
    } else {
        let mut temp_nat = result_nat;
        while temp_nat > (0 as nat) {
            if temp_nat % (2 as nat) == (1 as nat) {
                bit_string.push('1');
            } else {
                bit_string.push('0');
            }
            temp_nat = temp_nat / (2 as nat);
        }
    }
    bit_string.reverse();
    bit_string
}
// </vc-code>

fn main() {}
}

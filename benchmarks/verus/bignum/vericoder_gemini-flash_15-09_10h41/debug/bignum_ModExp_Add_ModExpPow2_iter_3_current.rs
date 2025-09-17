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
/* helper modified by LLM (iteration 3): Fixed type annotation for literal 1 */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat
    requires
        z > 1,
    decreases y
{
    if y == 0 { 1nat % z } else { (x * ModExp(x, (y - 1) as nat, z)) % z }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed type mismatches in ModExp_Add_ModExpPow2 */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    let result_int = ModExp(x_int, y_int, z_int);

    // Convert the 'result_int' (nat) back to a bit string representation (Vec<char>).
    // This part requires a helper function for int to bit string conversion.
    let mut result_vec = Vec::<char>::new();
    let mut temp: nat = result_int; // Explicitly declare temp as nat
    if temp == 0_nat {
        result_vec.push('0');
    } else {
        while temp > 0_nat
            invariant
                temp >= 0_nat,
        {
            if temp % 2_nat == 1_nat { // Explicitly define 1 as nat
                result_vec.push('1');
            } else {
                result_vec.push('0');
            }
            temp = temp / 2_nat;
        }
    }
    
    result_vec.reverse();
    result_vec
}
// </vc-code>

fn main() {}
}

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
/* helper modified by LLM (iteration 2): Fixed type inference for literal 1 */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat
    requires z > 1
    decreases y
{
    if y == 0 { 1nat % z } else if y % 2 == 0 { ModExp(x * x % z, y / 2, z) % z } else { x * ModExp(x * x % z, y / 2, z) % z }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed type mismatches on `num` to `nat` and added invariant for `num` in while loop */
{
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);
    let result_nat = ModExp(x, y, z);
    let mut res = Vec::<char>::new();
    let mut num: nat = result_nat;
    if num == 0 {
        res.push('0');
    } else {
        while num > 0
            invariant
                num.is_constant() || num.is_literal() || num.is_variable_of_type_nat(), // Ensure num remains nat type
                num >= 0,
        {
            if num % 2 == 0 {
                res.insert(0, '0');
            } else {
                res.insert(0, '1');
            }
            num = num / 2;
        }
    }
    res
}
// </vc-code>

fn main() {}
}

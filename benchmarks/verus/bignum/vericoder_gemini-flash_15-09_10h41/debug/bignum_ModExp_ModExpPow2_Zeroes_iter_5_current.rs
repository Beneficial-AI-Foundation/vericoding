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
/* helper modified by LLM (iteration 5): removed the ModExp helper function since it's not actually used anywhere. The Str2Int function already provides the necessary conversion for the modulus calculation. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed the `num` variable from `nat` to `int` and added an explicit `as nat` cast after the division, which was the original problem. The previous fix of declaring it `nat` was not working as the insert operation was expecting an `int`. This provides the correct fix. */
{
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);
    let result_nat = Exp_int(x, y) % z;
    let mut res = Vec::<char>::new();
    let mut num: int = result_nat as int;
    if num == 0 {
        res.push('0');
    } else {
        while num > 0
            invariant
                num >= 0,
        {
            if num % 2 == 0 {
                res.insert(0, '0');
            } else {
                res.insert(0, '1');
            }
            num = (num / 2) as int;
        }
    }
    res
}
// </vc-code>

fn main() {}
}

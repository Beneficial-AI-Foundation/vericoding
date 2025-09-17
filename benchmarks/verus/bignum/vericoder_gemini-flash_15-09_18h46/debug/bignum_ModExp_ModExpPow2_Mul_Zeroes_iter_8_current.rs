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
/* helper modified by LLM (iteration 8): Fixed type inference for literal `1`. */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat {
    if y == 0 {
        1nat % z
    } else if y % 2 == 0 {
        ModExp(x * x % z, y / 2, z)
    } else {
        x * ModExp(x * x % z, y / 2, z) % z
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Fixed type mismatches by explicitly casting to `nat` where needed. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);
    let result_int = ModExp(x_int, y_int, z_int);

    let mut result_vec = Vec::<char>::new();
    let mut temp: nat = result_int;
    if temp == 0nat {
        result_vec.insert(0, '0');
    } else {
        while temp > 0nat
            invariant
                forall |i: int| 0 <= i && i < result_vec.len() ==> (result_vec@[i] == '0' || result_vec@[i] == '1'),
                temp >= 0nat
            decreases temp
        {
            if temp % 2nat == 0nat {
                result_vec.insert(0, '0');
            } else {
                result_vec.insert(0, '1');
            }
            temp = (temp / 2nat) as nat;
        }
    }
    result_vec
}
// </vc-code>

fn main() {}
}

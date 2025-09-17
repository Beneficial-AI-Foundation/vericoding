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
/* helper modified by LLM (iteration 4): Removed placeholder and provided an empty helper section as no custom helpers are needed. */
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed compilation error: ensured `if y == 0 nat` has curly braces for its body, properly declared `res_nat` with `nat` type. */
{
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let z: nat = Str2Int(sz@);

    if y == (0 as nat) {
        let mut vec_result = Vec::<char>::new();
        vec_result.push('1');
        return vec_result;
    }

    let mut result_x: nat = x % z;
    let mut result_y: nat = y;
    let mut res_nat: nat = 1_nat; // 1 as nat

    while result_y > (0 as nat)
        invariant
            z > (1 as nat),
            // result_x is always x^(2^k) % z, and res_nat is the product of those result_x terms where the corresponding bit in y is 1
        decreases result_y
    {
        if result_y % (2 as nat) == (1 as nat) {
            res_nat = (res_nat * result_x) % z;
        }
        result_x = (result_x * result_x) % z;
        result_y = result_y / (2 as nat);
    }

    // Convert res_nat back to a bit string (Vec<char>)
    let mut res_vec = Vec::<char>::new();
    if res_nat == (0 as nat) {
        res_vec.push('0');
    } else {
        let mut temp_nat: nat = res_nat;
        while temp_nat > (0 as nat)
            invariant
                temp_nat >= (0 as nat),
            decreases temp_nat
        {
            if temp_nat % (2 as nat) == (1 as nat) {
                res_vec.push('1');
            } else {
                res_vec.push('0');
            }
            temp_nat = temp_nat / (2 as nat);
        }
        res_vec.reverse();
    }

    res_vec
}
// </vc-code>

fn main() {}
}

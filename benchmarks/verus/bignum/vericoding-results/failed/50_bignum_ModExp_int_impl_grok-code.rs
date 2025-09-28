// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fix ensures block format and update comment to iteration 10 */
spec fn exp_mod_spec(x: nat, exp: nat, z: nat) -> nat
    decreases exp
    ensures
        exp_mod_spec(x, exp, z) < z,
{
    if exp == 0 {
        1
    } else if (exp % 2) == 1 {
        let r = exp_mod_spec(x, (exp - 1) as nat, z);
        let xr = x % z;
        (r * xr % z)
    } else {
        let new_x = (x * x % z);
        exp_mod_spec(new_x, (exp / 2) as nat, z)
    }
}

fn exp_mod(x: u64, exp: u64, z: u64) -> (result: u64)
    requires z > 1,
    ensures result as nat == (exp_int(x as nat, exp as nat) % z as nat),
        result as nat < z as nat,
    decreases exp,
{
    if exp == 0 {
        1
    } else if (exp % 2) == 1 {
        let r = exp_mod(x, exp - 1, z);
        let xr = (x % z);
        ((r as u128 * xr as u128 % z as u128) as u64)
    } else {
        let new_x = ((x as u128 * x as u128 % z as u128) as u64);
        exp_mod(new_x, (exp / 2), z)
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_int(x: u64, y: u64, n: u64, z: u64) -> (res: u64)
    requires 
        y < exp_int(x as nat, y as nat),
        z > 1,
    ensures res as nat == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): update comment to iteration 10 */
{
    exp_mod(x, y, z)
}
// </vc-code>


}

fn main() {}
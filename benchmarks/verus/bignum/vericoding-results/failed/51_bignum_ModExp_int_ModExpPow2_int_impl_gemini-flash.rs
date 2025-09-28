// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
    decreases y
{
    if y == 0 { 1 } else { x * exp_int(x, (y - 1) as nat) }
}

fn mod_exp_pow2_int(x: nat, y: nat, n: nat, z: nat) -> (res: nat)
    requires 
        y == exp_int(2, n),
        z > 0,
    ensures res == exp_int(x, y) % z
    decreases n
{
    assume(false);
    unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed explicit casting of `y - 1` to `nat` within `exp_mod_spec` to avoid compilation errors, as `y` is already `nat`, so `y - 1` will also be `nat`. */
spec fn exp_mod_spec(x: nat, y: nat, z: nat)
    decreases y
{
    if y == 0 {
        1 % z
    } else {
        (x * exp_mod_spec(x, y - 1, z)) % z
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_int(x: u8, y: u8, n: u8, z: u8) -> (res: u8)
    requires 
        (y as nat) < exp_int(2nat, (n as nat) + 1nat),
        (z as nat) > 1,
    ensures (res as nat) == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed type mismatch issues by ensuring all internal calculations involving `half_y_limit` and `y` are performed as `nat` types where required, converting to `u8` only for executable function calls. Removed unnecessary `as nat` casts on `y` for comparison and subtraction, as `y` is already `u8` and needs to be coerced to `nat` for spec functions like `exp_int` directly, or for comparison to other `nat` types. */
{
    if n == 0 {
        (x % z) as u8
    } else {
        let n_minus_1 = (n - 1) as u8;
        let half_y_limit: nat;
        proof {
            half_y_limit = exp_int(2, (n as nat) - 1);
        }

        if (y as nat) < half_y_limit {
            mod_exp_int(x, y, n_minus_1, z)
        } else {
            let y_prime_nat = (y as nat) - half_y_limit;
            let y_prime_u8 = y_prime_nat as u8;
            let term1 = mod_exp_int(x, y_prime_u8, n_minus_1, z);
            let term2: nat;
            proof {
                term2 = mod_exp_pow2_int(x as nat, half_y_limit, (n as nat) - 1, z as nat);
            }
            let term2_u8 = term2 as u8;

            let result_u8 = ((term1 as u16 * term2_u8 as u16) % (z as u16)) as u8;
            result_u8
        }
    }
}
// </vc-code>


}

fn main() {}
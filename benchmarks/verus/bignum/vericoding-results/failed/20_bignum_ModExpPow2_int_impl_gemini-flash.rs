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
/* helper modified by LLM (iteration 10): no changes */
spec fn exp_mod_int(x: nat, y: nat, z: nat) -> nat
    decreases y
{
    if y == 0 {
        1 % z
    } else {
        (x * exp_mod_int(x, (y - 1) as nat, z)) % z
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2_int(x: u8, y: u8, n: u8, z: u8) -> (res: u8)
    requires 
        y as nat == exp_int(2, n as nat),
        z > 0,
    ensures res as nat == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Removed `nat` casts in executable code. */
{
    if n == 0 {
        (x % z) as u8
    } else {
        let prev_y_val = (1u8 << (n - 1));
        let prev_n = n - 1;

        let prev_res = mod_exp_pow2_int(x, prev_y_val, prev_n, z);

        let term1 = prev_res as u128;
        let term2 = prev_res as u128;
        let modulus = z as u128;

        let result = (term1 * term2) % modulus;

        result as u8
    }
}
// </vc-code>


}

fn main() {}
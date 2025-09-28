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
{
    /* code modified by LLM (iteration 10): use u32 for arithmetic to avoid overflow in exec code */
    if n == 0 {
        ((x as u32 % z as u32) as u8)
    } else {
        let half_pow_u32 = mod_exp_pow2_int(x, (y / 2) as u8, n - 1, z) as u32;
        let z_u32 = z as u32;
        let square_mod_u32 = (half_pow_u32 * half_pow_u32) % z_u32;
        if n % 2 == 0 {
            (square_mod_u32 as u8)
        } else {
            let x_u32 = x as u32;
            let next_mod_u32 = (square_mod_u32 * x_u32) % z_u32;
            (next_mod_u32 as u8)
        }
    }
}
// </vc-code>


}

fn main() {}
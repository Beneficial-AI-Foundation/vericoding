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
/* helper modified by LLM (iteration 10): Fixed type mismatch errors in mod_exp by ensuring consistent type usage for intermediate calculations and modulo results. */
spec fn exp_mod(x: u64, y: u64, n: u64) -> u64
    decreases y
{
    if y == 0 {
        1u64
    } else if y % 2 == 0 {
        let half: u64 = exp_mod(x, y / 2, n);
        (((half as u128) * (half as u128)) % (n as u128)) as u64
    } else {
        let exp_term: u64 = exp_mod(x, (y - 1) as u64, n);
        (((x as u128) * (exp_term as u128)) % (n as u128)) as u64
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
/* code modified by LLM (iteration 10): Calls exp_mod with the correct parameters. */
{
    exp_mod(x, y, z)
}
// </vc-code>


}

fn main() {}
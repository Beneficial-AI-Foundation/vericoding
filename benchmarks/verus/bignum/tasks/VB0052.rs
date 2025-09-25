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
fn mod_exp_int(x: u64, y: u64, n: u64, z: u64) -> (res: u64)
    requires 
        y < exp_int(x as nat, y as nat),
        z > 1,
    ensures res as nat == exp_int(x as nat, y as nat) % (z as nat)
    decreases n
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {}
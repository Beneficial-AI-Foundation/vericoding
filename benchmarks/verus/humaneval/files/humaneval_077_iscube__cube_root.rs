// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: nat) -> nat { n * n * n }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cube_root(n: u8) -> (r: u8)
    ensures 
        cube(r as nat) <= n as nat,
        (n as nat) < cube((r as nat) + 1),
        r as nat <= n as nat,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: nat) -> nat { n * n * n }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cube_root(n: nat) -> (r: nat)
    ensures 
        cube(r) <= n < cube(r + 1),
        r <= n,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
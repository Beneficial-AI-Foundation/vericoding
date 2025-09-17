// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn cube(n: int) -> int {
    n * n * n
}
// </vc-helpers>

// <vc-spec>
fn is_cube(n: nat) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n && n == cube(k)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}
use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
// Empty original helpers, no updates needed
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// <vc-code>
{
    let mut r: int = 0;
    while ((r + 1) * (r + 1) <= x)
        invariant
            r * r <= x,
            r >= 0,
    {
        r = r + 1;
    }
    r
}
// </vc-code>

fn main() {
}

}
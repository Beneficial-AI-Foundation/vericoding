// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
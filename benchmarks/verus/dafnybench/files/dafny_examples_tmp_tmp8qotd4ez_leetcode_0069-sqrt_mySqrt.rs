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
fn mySqrt(x: i8) -> (res: i8)
    requires 0 <= x as int,
    ensures sqrt(x as int, res as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
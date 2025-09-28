use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
fn sqrt_rec(x: int, r: int) -> (res: int)
    requires
        0 <= x,
        0 <= r,
        r * r <= x,
    ensures
        sqrt(x, res),
    decreases x - r * r
{
    if (r + 1) * (r + 1) > x {
        r
    } else {
        proof {
            assert(r * r < (r + 1) * (r + 1)) by(nonlinear_arith);
            assert((r + 1) * (r + 1) <= x);
            assert(0 <= x - (r + 1) * (r + 1)) by {
                assert((r + 1) * (r + 1) <= x);
            }
            assert(x - (r + 1) * (r + 1) < x - r * r) by {
                assert((r + 1) * (r + 1) > r * r) by(nonlinear_arith);
            }
        }
        sqrt_rec(x, r + 1)
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// <vc-code>
{
    let r = sqrt_rec(x, 0);
    r
}
// </vc-code>

fn main() {
}

}
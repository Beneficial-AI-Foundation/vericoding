use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
proof fn mul_ge_self(k: int)
    requires k >= 0,
    ensures k * k >= k
{
    if k == 0 {
        assert(k * k == 0);
    } else {
        // k >= 1, so k-1 >= 0 and k*(k-1) >= 0
        assert(k - 1 >= 0);
        assert(k * (k - 1) >= 0);
        assert(k * k == k * (k - 1) + k);
        assert(k * k >= k);
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
    let mut r: int = 0;
    while (r + 1) * (r + 1) <= x
        invariant 0 <= r && r * r <= x && r <= x,
        decreases x - r
    {
        assert(r + 1 >= 0);
        mul_ge_self(r + 1);
        assert((r + 1) <= (r + 1) * (r + 1));
        assert((r + 1) <= x);
        r = r + 1;
    }
    return r;
}
// </vc-code>

fn main() {
}

}
use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let N: int = n as int;
    let mut r: int = 0;
    while (r + 1) * (r + 1) <= N
        invariant 0 <= r && r <= N && r * r <= N
        decreases N - r
    {
        r = r + 1;
    }
    // post-loop: r*r <= N and not ((r+1)*(r+1) <= N) i.e., N < (r+1)*(r+1)
    assert(r * r <= N);
    assert(!( (r + 1) * (r + 1) <= N ));
    let res: i32 = r as i32;
    proof {
        // connect int arithmetic to i32 arithmetic for the postconditions
        assert((res as int) * (res as int) == r * r);
        assert((res + 1) as int * (res + 1) as int == (r + 1) * (r + 1));
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}
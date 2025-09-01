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
    let n64: i64 = n as i64;
    let mut r: i32 = 0;
    let mut i: i32 = 0;
    while i < n && ((r as i64) + 1) * ((r as i64) + 1) <= n64
        invariant 0 <= i;
        invariant i <= n;
        invariant r == i;
        invariant (r as i64) * (r as i64) <= n64;
        decreases n - i;
    {
        r = r + 1;
        i = i + 1;
    }
    let res: i32 = r;
    proof {
        // use mathematical integers for the postcondition proofs
        assert((res as i64) * (res as i64) <= n64);
        // cast i64 comparisons to mathematical ints
        assert(((res as i64) * (res as i64)) as int == (res as int) * (res as int));
        assert((n64 as int) == (n as int));
        assert((res as int) * (res as int) <= (n as int));
        // show the next square is greater than n
        // From loop exit, either i >= n (hence r == n, so (r+1)^2 > n) or the square check failed
        assert(!((((res as i64) + 1) * ((res as i64) + 1)) <= n64));
        assert(!((((res as int) + 1) * ((res as int) + 1)) <= (n as int)));
    }
    res
    // impl-end
}
// </vc-code>

fn main() {}
}
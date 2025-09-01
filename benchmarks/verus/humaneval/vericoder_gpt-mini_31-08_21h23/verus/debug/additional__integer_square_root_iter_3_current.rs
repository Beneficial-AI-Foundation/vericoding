use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
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
    let mut r: i64 = 0;
    let n64: i64 = n as i64;
    while (r + 1) * (r + 1) <= n64
        invariant 0 <= r && r * r <= n64 && r <= n64
        decreases n64 - r
    {
        r = r + 1;
    }
    // Prove the postconditions in a proof block to help the verifier
    proof {
        // r is non-negative and r*r <= n64 from the invariant
        assert(r * r <= n64);
        // The loop exits when (r+1)^2 > n64, i.e., not ((r+1)^2 <= n64)
        assert(!((r + 1) * (r + 1) <= n64));
        // Convert to i32 for the postcondition statements
        let res_i32: i32 = r as i32;
        let res_i64: i64 = res_i32 as i64;
        assert(res_i64 * res_i64 <= n64);
        assert(n64 < (res_i64 + 1) * (res_i64 + 1));
    }
    r as i32
}
// </vc-code>

fn main() {}
}
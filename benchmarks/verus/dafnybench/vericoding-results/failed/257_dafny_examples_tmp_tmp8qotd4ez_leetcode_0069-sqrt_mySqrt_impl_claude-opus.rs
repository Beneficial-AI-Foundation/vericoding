use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
proof fn sqrt_unique(x: int, r1: int, r2: int)
    requires
        sqrt(x, r1),
        sqrt(x, r2),
    ensures
        r1 == r2,
{
    // If both r1 and r2 satisfy sqrt, they must be equal
    if r1 < r2 {
        // r1 + 1 <= r2
        // So (r1 + 1) * (r1 + 1) <= r2 * r2 <= x
        // But sqrt(x, r1) says (r1 + 1) * (r1 + 1) > x
        assert((r1 + 1) * (r1 + 1) <= r2 * r2);
        assert(r2 * r2 <= x);
        assert((r1 + 1) * (r1 + 1) > x);
        assert(false);
    } else if r2 < r1 {
        // Symmetric argument
        assert((r2 + 1) * (r2 + 1) <= r1 * r1);
        assert(r1 * r1 <= x);
        assert((r2 + 1) * (r2 + 1) > x);
        assert(false);
    }
}

proof fn sqrt_monotone_helper(a: int, b: int)
    requires
        0 <= a <= b,
    ensures
        a * a <= b * b,
{
    assert(a * a == a * a);
    assert(b * b == b * b);
    if a < b {
        assert(a * a <= a * b);
        assert(a * b < b * b);
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
    if x == 0 {
        return 0;
    }
    
    let mut low: int = 0;
    let mut high: int = x;
    let mut result: int = 0;
    
    while low <= high
        invariant
            0 <= low,
            0 <= high,
            high <= x,
            0 <= result,
            result * result <= x,
            forall|r: int| 0 <= r < low ==> !sqrt(x, r),
            forall|r: int| high < r <= x ==> !sqrt(x, r),
    {
        let mid = low + (high - low) / 2;
        assert(low <= mid <= high);
        
        if mid * mid <= x {
            result = mid;
            if (mid + 1) * (mid + 1) > x {
                // Found exact answer
                assert(sqrt(x, mid));
                return mid;
            }
            low = mid + 1;
            assert(forall|r: int| 0 <= r < low ==> !sqrt(x, r)) by {
                assert(forall|r: int| 0 <= r < mid ==> !sqrt(x, r));
                assert(!sqrt(x, mid));
            };
        } else {
            high = mid - 1;
            assert(forall|r: int| high < r <= x ==> !sqrt(x, r)) by {
                assert(forall|r: int| mid <= r <= x ==> !sqrt(x, r)) by {
                    assert(mid * mid > x);
                    assert(forall|r: int| mid <= r <= x ==> r * r >= mid * mid);
                };
            };
        }
    }
    
    assert(sqrt(x, result));
    result
}
// </vc-code>

fn main() {
}

}
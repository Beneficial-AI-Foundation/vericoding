use vstd::prelude::*;

verus! {

// Author: Shaobo He

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}

// <vc-helpers>
proof fn lemma_sqrt_monotonic(x: int, r1: int, r2: int)
    requires 0 <= x, 0 <= r1, 0 <= r2, r1 < r2, sqrt(x, r1)
    ensures r2 * r2 > x
{
    assert(sqrt(x, r1) ==> (r1 + 1) * (r1 + 1) > x);
    assert(r1 + 1 <= r2);
    assert((r1 + 1) * (r1 + 1) <= r2 * r2);
}

proof fn lemma_sqrt_unique(x: int, r1: int, r2: int)
    requires 0 <= x, 0 <= r1, 0 <= r2, sqrt(x, r1), sqrt(x, r2)
    ensures r1 == r2
{
    if r1 < r2 {
        lemma_sqrt_monotonic(x, r1, r2);
        assert(false);
    }
    if r2 < r1 {
        lemma_sqrt_monotonic(x, r2, r1);
        assert(false);
    }
}

proof fn lemma_binary_search_bounds(x: int, low: int, high: int)
    requires 0 <= x, 0 <= low, low <= high, low * low <= x, (high + 1) * (high + 1) > x
    ensures exists|r: int| low <= r <= high && sqrt(x, r)
{
    let mid = (low + high) / 2;
    if low == high {
        assert(sqrt(x, low));
    } else if mid * mid <= x {
        if (mid + 1) * (mid + 1) > x {
            assert(sqrt(x, mid));
        } else {
            lemma_binary_search_bounds(x, mid + 1, high);
        }
    } else {
        lemma_binary_search_bounds(x, low, mid - 1);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if x == 0 {
        return 0;
    }
    
    let mut low = 0;
    let mut high = x;
    
    while high - low > 1
        invariant {
            0 <= low <= high <= x &&
            low * low <= x &&
            (high + 1) * (high + 1) > x
        }
    {
        let mid = (low + high) / 2;
        if mid * mid <= x {
            low = mid;
        } else {
            high = mid - 1;
        }
    }
    
    if high * high <= x {
        proof {
            assert((high + 1) * (high + 1) > x);
        }
        high
    } else {
        proof {
            assert(low * low <= x);
            assert((low + 1) * (low + 1) > x);
        }
        low
    }
}
// </vc-code>

fn main() {
}

}
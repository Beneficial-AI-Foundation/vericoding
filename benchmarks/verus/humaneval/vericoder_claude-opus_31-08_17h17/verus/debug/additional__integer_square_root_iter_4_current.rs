use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish that if mid * mid <= n and (mid + 1) * (mid + 1) > n, then mid is the square root
proof fn square_root_unique(n: i32, mid: i32)
    requires
        n >= 1,
        mid >= 0,
        mid * mid <= n,
        n < (mid + 1) * (mid + 1),
    ensures
        forall|k: i32| #[trigger] (k * k) <= n && k >= 0 ==> k <= mid,
{
    // By contradiction: if there exists k > mid with k * k <= n,
    // then k >= mid + 1, so k * k >= (mid + 1) * (mid + 1) > n
    // which contradicts k * k <= n
}

// Helper lemma for the loop invariant maintenance
proof fn binary_search_invariant_maintained(n: i32, low: i32, high: i32, mid: i32)
    requires
        n >= 1,
        0 <= low <= high,
        low * low <= n,
        n < (high + 1) * (high + 1),
        mid == low + (high - low) / 2,
    ensures
        low <= mid <= high,
{
    // This follows from integer division properties
}
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
    let mut low: i32 = 0;
    let mut high: i32 = n;
    
    // Initial assertions to establish loop invariants
    assert(low * low == 0 <= n);
    assert(n < (n + 1) * (n + 1)) by {
        assert(n >= 1);
        assert((n + 1) * (n + 1) == n * n + 2 * n + 1);
        assert(n * n + 2 * n + 1 > n * n + n);
        assert(n * n + n >= n);
    }
    
    while low < high
        invariant
            0 <= low <= high,
            low * low <= n,
            n < (high + 1) * (high + 1),
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        proof {
            binary_search_invariant_maintained(n, low, high, mid);
        }
        
        if (mid + 1) * (mid + 1) <= n {
            // mid is too small, search in upper half
            assert((mid + 1) * (mid + 1) <= n);
            assert(mid + 1 > low);
            low = mid + 1;
        } else {
            // mid might be the answer or too large, search in lower half
            assert(n < (mid + 1) * (mid + 1));
            assert(mid < high);
            high = mid;
        }
    }
    
    // When low == high, we have found the square root
    assert(low == high);
    assert(low * low <= n);
    assert(n < (low + 1) * (low + 1));
    
    low
}
// </vc-code>

fn main() {}
}
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
        forall|k: i32| 0 <= k && #[trigger] (k * k) <= n ==> k <= mid,
{
    assert forall|k: i32| 0 <= k && #[trigger] (k * k) <= n implies k <= mid by {
        if k > mid {
            assert(k >= mid + 1);
            assert(k * k >= (mid + 1) * (mid + 1));
            assert((mid + 1) * (mid + 1) > n);
            assert(k * k > n);
        }
    }
}

// Helper lemma for the loop invariant maintenance
proof fn binary_search_invariant_maintained(n: i32, low: i32, high: i32, mid: i32)
    requires
        0 <= low <= high,
        low * low <= n,
        n < (high + 1) * (high + 1),
        mid == low + (high - low) / 2,
    ensures
        low <= mid <= high,
{
    // This follows from integer division properties
    assert((high - low) / 2 >= 0);
    assert((high - low) / 2 <= high - low);
}

// Helper lemma to prove n < (n+1)*(n+1) for n >= 1
proof fn square_bound_lemma(n: i32)
    requires
        n >= 1,
    ensures
        n < (n + 1) * (n + 1),
{
    assert((n + 1) * (n + 1) == n * n + 2 * n + 1);
    assert(2 * n + 1 >= 3);
    assert(n * n + 2 * n + 1 > n * n + n);
    assert(n * n + n >= n);
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
    assert(low * low == 0);
    assert(0 <= n);
    
    proof {
        square_bound_lemma(n);
    }
    assert(n < (n + 1) * (n + 1));
    assert(n < (high + 1) * (high + 1));
    
    while low < high
        invariant
            0 <= low <= high <= n,
            low * low <= n,
            n < (high + 1) * (high + 1),
        decreases high - low,
    {
        let mid = low + (high - low) / 2;
        proof {
            binary_search_invariant_maintained(n, low, high, mid);
        }
        
        // Check for overflow before computing (mid + 1) * (mid + 1)
        if mid < n && (mid + 1) <= n {
            let mid_plus_one_squared = (mid + 1) * (mid + 1);
            if mid_plus_one_squared <= n {
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
        } else {
            // mid + 1 > n, so (mid + 1) * (mid + 1) > n
            assert(mid >= n || mid + 1 > n);
            assert(n < (mid + 1) * (mid + 1));
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
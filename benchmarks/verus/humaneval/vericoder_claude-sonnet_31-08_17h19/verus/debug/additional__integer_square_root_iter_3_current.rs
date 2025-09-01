use vstd::prelude::*;

verus! {

// <vc-helpers>
lemma lemma_sqrt_bounds(n: i32, x: i32)
    requires n >= 1, x >= 0, x <= n
    ensures x * x <= n * n
{
}

lemma lemma_mid_bounds(low: i32, high: i32, n: i32)
    requires 0 <= low <= high <= n, n >= 1
    ensures 
        low + (high - low + 1) / 2 >= 0,
        low + (high - low + 1) / 2 <= n + 1,
        (low + (high - low + 1) / 2) * (low + (high - low + 1) / 2) >= 0
{
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
    let mut low = 0;
    let mut high = n;
    
    // Establish initial invariant
    assert(low * low <= n);
    assert(n < (high + 1) * (high + 1)) by {
        assert(n < (n + 1) * (n + 1));
        assert((n + 1) * (n + 1) == n * n + 2 * n + 1);
        assert(n * n + 2 * n + 1 > n);
    }
    
    while low < high
        invariant
            0 <= low <= high <= n,
            low * low <= n,
            n < (high + 1) * (high + 1),
        decreases high - low,
    {
        proof {
            lemma_mid_bounds(low, high, n);
        }
        
        let mid = low + (high - low + 1) / 2;
        
        assert(mid >= 0);
        assert(mid <= n + 1);
        
        if mid <= 46340 && mid * mid <= n {
            low = mid;
        } else {
            high = mid - 1;
            assert(n < mid * mid);
            assert(n < (high + 1) * (high + 1)) by {
                assert(high + 1 == mid);
            }
        }
    }
    
    low
}
// </vc-code>

fn main() {}
}
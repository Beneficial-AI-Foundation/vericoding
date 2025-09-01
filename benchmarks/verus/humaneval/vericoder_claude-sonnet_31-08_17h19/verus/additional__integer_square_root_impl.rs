use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sqrt_bounds(n: i32, x: i32)
    requires n >= 1, x >= 0, x <= n
    ensures x * x <= n * n
{
}

proof fn lemma_mid_bounds(low: i32, high: i32, n: i32)
    requires 0 <= low <= high <= n, n >= 1
    ensures 
        low + (high - low + 1) / 2 >= 0,
        low + (high - low + 1) / 2 <= n + 1,
        (low + (high - low + 1) / 2) * (low + (high - low + 1) / 2) >= 0
{
}

proof fn lemma_overflow_safe(x: i32)
    requires x <= 46340
    ensures x * x <= 2147395600
{
}

proof fn lemma_initial_bounds(n: i32)
    requires n >= 1
    ensures 
        0i32 * 0i32 <= n,
        n < (n + 1) * (n + 1)
{
    assert(0i32 * 0i32 == 0);
    assert((n + 1) * (n + 1) == n * n + 2 * n + 1);
    assert(n * n + 2 * n + 1 > n);
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
    
    proof {
        lemma_initial_bounds(n);
    }
    
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
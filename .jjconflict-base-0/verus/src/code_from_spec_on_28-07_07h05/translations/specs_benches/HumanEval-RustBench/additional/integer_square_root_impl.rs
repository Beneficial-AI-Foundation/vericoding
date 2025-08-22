use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn add_one(n: i32) -> (result: i32)
    ensures
        result == n + 1,
{
    return 0;  // TODO: Remove this line and implement the function body
}

#[verifier::external_body]
fn square(n: i32) -> (result: i32)
    ensures
        n * n == result,
{
    return 0;  // TODO: Remove this line and implement the function body
}

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
{
    let mut low = 1i32;
    /* code modified by LLM (iteration 1): initialize high properly to satisfy initial invariant */
    let mut high = if n <= 46340 { n } else { 46340 }; // 46340^2 < 2^31 - 1
    
    /* code modified by LLM (iteration 1): ensure initial invariant holds */
    if n >= (high + 1) * (high + 1) {
        high = 46340; // This ensures n < (high + 1) * (high + 1) since 46341^2 > 2^31 - 1 > n
    }
    
    /* code modified by LLM (iteration 1): updated invariants with proper bounds */
    while low <= high
        invariant
            1 <= low <= high + 1,
            high >= 1,
            high <= 46340,
            (low - 1) * (low - 1) <= n,
            n < (high + 1) * (high + 1)
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        /* code modified by LLM (iteration 1): prove bounds to prevent overflow */
        assert(low <= mid <= high);
        assert(mid <= 46340);
        assert(mid * mid <= 46340 * 46340);
        let mid_squared = mid * mid;
        
        if mid_squared == n {
            /* code modified by LLM (iteration 1): prove postcondition for exact square root case */
            assert(mid * mid <= n);
            assert(mid * mid == n);
            // Need to prove n < (mid + 1) * (mid + 1)
            // Since mid * mid == n, we have n < (mid + 1) * (mid + 1) = mid * mid + 2 * mid + 1 = n + 2 * mid + 1
            assert(n < n + 2 * mid + 1);
            return mid;
        } else if mid_squared < n {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 1): prove postcondition when loop ends */
    assert(low > high);
    assert((low - 1) * (low - 1) <= n);
    assert(n < (high + 1) * (high + 1));
    assert(low == high + 1);
    // Therefore (high * high) <= n < (high + 1) * (high + 1)
    assert(high * high <= n);
    high
}

fn main() {}
}

The key changes I made:
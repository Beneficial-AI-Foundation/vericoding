use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn add_one(n: i32) -> (result: i32)
    ensures
        result == n + 1,
{
    n + 1
}

#[verifier::external_body]
fn square(n: i32) -> (result: i32)
    ensures
        n * n == result,
{
    n * n
}

fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
{
    let mut low = 0i32;
    /* code modified by LLM (iteration 3): set high to safe upper bound */
    let mut high = 46340i32; // sqrt(2^31-1) ≈ 46340
    
    /* code modified by LLM (iteration 3): ensure initial high satisfies n < (high + 1) * (high + 1) with overflow checks */
    while high > 0 && high < 46340 && n >= (high + 1) * (high + 1)
        invariant
            high >= 0,
            high <= 46340,
        decreases high
    {
        high = high - 1;
    }
    
    /* code modified by LLM (iteration 3): updated loop with corrected invariants and overflow protection */
    while low <= high
        invariant
            0 <= low,
            high >= -1,
            low <= high + 1,
            high <= 46340,
            low <= 46340,
            low == 0 || (low - 1) * (low - 1) <= n,
            high == -1 || (high <= 46340 && n < (high + 1) * (high + 1)),
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        /* code modified by LLM (iteration 3): safe multiplication with explicit bounds */
        assert(mid <= high);
        assert(high <= 46340);
        assert(mid <= 46340);
        assert(mid * mid <= 46340 * 46340);
        let mid_squared = mid * mid;
        
        if mid_squared == n {
            /* code modified by LLM (iteration 3): verify postconditions before returning mid */
            assert(mid * mid == n);
            assert(mid * mid <= n);
            assert(mid <= 46340);
            assert((mid + 1) * (mid + 1) > mid * mid);
            assert(n < (mid + 1) * (mid + 1));
            return mid;
        } else if mid_squared < n {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 3): handle case when loop terminates normally */
    assert(low > high);
    assert(low > 0); // since we start with low=0 and increment it
    let result = low - 1;
    assert(result >= 0);
    assert(result * result <= n); // from loop invariant
    assert(n < (result + 1) * (result + 1)); // from loop invariant
    result
}

fn main() {}
}

The key fixes I made:
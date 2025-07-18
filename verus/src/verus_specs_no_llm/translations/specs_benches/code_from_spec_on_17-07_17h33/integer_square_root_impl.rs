use vstd::prelude::*;

verus! {

//ATOM
#[verifier::external_body]
fn add_one(n: i32) -> (result: i32)
    ensures
        result == n + 1,
{
    return 0;  // TODO: Remove this line and implement the function body
}

//ATOM
#[verifier::external_body]
fn square(n: i32) -> (result: i32)
    ensures
        n * n == result,
{
    return 0;  // TODO: Remove this line and implement the function body
}

//IMPL integer_square_root
/* code modified by LLM (iteration 3): Fixed initial invariant establishment, added overflow checks, and corrected postcondition logic */
fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
{
    let mut low = 1i32;
    let mut high = n;
    
    /* code modified by LLM (iteration 3): Initialize high to ensure invariant holds initially */
    if n > 46340 {  // sqrt(i32::MAX) ≈ 46340
        high = 46340;
    }
    
    while low <= high
        invariant
            1 <= low,
            low <= high + 1,
            high <= n,
            high <= 46340,  // Prevent overflow
            (low - 1) * (low - 1) <= n,
            n < (high + 1) * (high + 1)
        decreases
            high - low + 1
    {
        let mid = low + (high - low) / 2;
        /* code modified by LLM (iteration 3): Added overflow protection for mid_squared calculation */
        let mid_squared = mid * mid;
        
        if mid_squared == n {
            /* code modified by LLM (iteration 3): Return mid only when it exactly satisfies postcondition */
            return mid;
        } else if mid_squared < n {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    /* code modified by LLM (iteration 3): Return high which satisfies all postconditions */
    return high;
}

fn main() {}
}
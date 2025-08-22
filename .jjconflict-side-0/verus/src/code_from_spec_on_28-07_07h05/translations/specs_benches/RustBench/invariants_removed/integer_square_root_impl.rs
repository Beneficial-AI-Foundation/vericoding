use vstd::prelude::*;

verus! {

//ATOM
#[verifier::external_body]
fn add_one(n: i32) -> (result: i32)
    ensures
        result == n + 1,
{
    n + 1
}

//ATOM
#[verifier::external_body]
fn square(n: i32) -> (result: i32)
    ensures
        n * n == result,
{
    n * n
}

//IMPL integer_square_root
fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
{
    /* code modified by LLM (iteration 4): initialize high to a smaller value to satisfy invariant */
    let mut low = 1i32;
    let mut high = if n <= 46340 { n } else { 46340 }; // 46340^2 < 2^31 - 1
    
    /* code modified by LLM (iteration 4): adjust high to ensure invariant holds initially */
    while high * high < n && high < 46340 {
        high = high + 1;
    }
    while (high + 1) * (high + 1) <= n && high > 1 {
        high = high - 1;
    }
    
    /* code modified by LLM (iteration 4): updated invariants and added overflow checks */
    while low <= high
        invariant
            1 <= low <= 46341,
            1 <= high <= 46340,
            low <= high + 1,
            (low - 1) * (low - 1) <= n,
            n < (high + 1) * (high + 1),
            high <= 46340, // prevent overflow
            low <= 46341   // prevent overflow
        decreases high - low + 1
    {
        let mid = low + (high - low) / 2;
        
        /* code modified by LLM (iteration 4): added overflow check before multiplication */
        if mid <= 46340 {
            let mid_squared = mid * mid;
            
            if mid_squared <= n {
                /* code modified by LLM (iteration 4): added overflow check for (mid + 1) * (mid + 1) */
                if mid < 46340 && (mid + 1) * (mid + 1) > n {
                    return mid;
                }
                low = mid + 1;
            } else {
                high = mid - 1;
            }
        } else {
            high = mid - 1;
        }
    }
    
    high
}

fn main() {}

} // end verus block

// The value 46340 is chosen because 46340^2 = 2,147,395,600 < 2,147,483,647 (which is 2^31 - 1, the maximum value for i32), ensuring no overflow occurs during multiplication operations.
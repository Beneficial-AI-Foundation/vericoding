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
    let mut high = n;
    
    while low <= high
        invariant
            0 <= low,
            low <= high + 1,
            high >= 0,
            low * low <= n,
            n < (high + 1) * (high + 1)
    {
        let mid = low + (high - low) / 2;
        
        if mid * mid <= n {
            if (mid + 1) * (mid + 1) > n {
                return mid;
            }
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }
    
    high
}

fn main() {}
}
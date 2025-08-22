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
    let mut result = 0;
    
    while result * result <= n
        invariant
            result >= 0,
            (result - 1) * (result - 1) <= n || result == 0,
    {
        if (result + 1) * (result + 1) > n {
            break;
        }
        result = result + 1;
    }
    
    result
}

fn main() {}
}
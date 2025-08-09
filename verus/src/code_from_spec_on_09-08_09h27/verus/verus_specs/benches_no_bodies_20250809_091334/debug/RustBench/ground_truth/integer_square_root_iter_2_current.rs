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
    let mut result = 1;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while result * result <= n && (result + 1) * (result + 1) <= n
        invariant
            result >= 1,
            result * result <= n,
        decreases n - result * result
    {
        result = result + 1;
    }
    result
}

fn main() {}
}
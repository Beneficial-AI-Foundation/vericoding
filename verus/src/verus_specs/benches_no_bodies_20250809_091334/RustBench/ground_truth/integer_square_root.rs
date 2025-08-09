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
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}
}
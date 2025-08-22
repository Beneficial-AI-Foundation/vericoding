use vstd::prelude::*;

verus! {
    fn square(n: u32) -> (r: u32)
        requires n <= 46340,
        ensures r == n * n,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

#[verifier::external]
fn main() {
    // TODO: Remove this comment and implement the function body
}
use vstd::prelude::*;

verus! {
    fn square(n: u32) -> (r: u32)
        requires n <= 46340,
        ensures r == n * n,
    {
        n * n
    }
}

#[verifier::external]
fn main() {
    let result = square(100);
    println!("Square of 100 is: {}", result);
}
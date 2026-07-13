// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sqrt(n: i32) -> (result: i32)
    ensures 
        result >= 0,
        n >= 0 ==> result * result <= n && (result + 1) * (result + 1) > n
{
    // impl-start
    assume(false);
    0
    // impl-end
}

fn check_sqrt_accuracy(scale: i32, tolerance: i32, numbers: Vec<i32>) -> (result: Vec<String>)
    requires 
        0 < tolerance,
        tolerance <= 100
    ensures 
        result.len() == numbers.len()
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {}
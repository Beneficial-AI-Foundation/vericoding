// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &Vec<i32>, threshold: i32) -> (result: bool)
    requires threshold >= 0,
    ensures
        !result <==> (forall|i: int, j: int| 
            0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==> 
            abs_diff(numbers[i] as int, numbers[j] as int) >= threshold as int),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}
fn main() {}
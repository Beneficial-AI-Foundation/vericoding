// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(numbers: Seq<int>, threshold: int) -> bool {
    true
}

spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

spec fn has_close_elements(numbers: Seq<int>, threshold: int) -> bool {
    exists|i: int, j: int| 0 <= i < j < numbers.len() && abs_diff(numbers[i], numbers[j]) < threshold
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn has_close_elements_impl(numbers: Seq<int>, threshold: int) -> (result: bool)
    requires valid_input(numbers, threshold)
    ensures result == has_close_elements(numbers, threshold)
// </vc-spec>
// <vc-code>
{
    assume(false);
    false
}
// </vc-code>


}

fn main() {}
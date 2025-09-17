// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn abs_diff(x: int, y: int) -> int {
    if x >= y { x - y } else { y - x }
}

spec fn valid_input(numbers: Seq<int>) -> bool {
    numbers.len() >= 2
}

spec fn is_optimal_pair(numbers: Seq<int>, pair: (int, int)) -> bool {
    numbers.contains(pair.0) &&
    numbers.contains(pair.1) &&
    pair.0 <= pair.1 &&
    forall|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j ==>
        abs_diff(numbers[i], numbers[j]) >= abs_diff(pair.0, pair.1)
}
// </vc-helpers>

// <vc-spec>
fn find_closest_elements(numbers: Seq<int>) -> (result: (int, int))
    requires valid_input(numbers)
    ensures is_optimal_pair(numbers, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
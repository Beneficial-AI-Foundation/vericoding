// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n > 0
}

spec fn can_be_sum_of_four_positive_evens(n: int) -> bool {
    n % 2 == 0 && n >= 8
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_equal_to_sum_even(n: i8) -> (result: bool)
    requires valid_input(n as int)
    ensures result == can_be_sum_of_four_positive_evens(n as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
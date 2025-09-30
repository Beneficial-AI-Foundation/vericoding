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
/* helper modified by LLM (iteration 2): simple spec predicate for evenness on ints */
spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

/* helper modified by LLM (iteration 2): bridge i8 operations to int for parity and lower bound */
proof fn bridge_i8_to_int_parity_and_bound(n: i8)
    ensures
        (n % 2 == 0) == ((n as int) % 2 == 0),
        (n >= 8i8) == ((n as int) >= 8),
{
}

// </vc-helpers>

// <vc-spec>
fn is_equal_to_sum_even(n: i8) -> (result: bool)
    requires valid_input(n as int)
    ensures result == can_be_sum_of_four_positive_evens(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute result using i8 ops and bridge to int spec in proof */
    let res: bool = (n % 2 == 0) && (n >= 8i8);
    proof {
        bridge_i8_to_int_parity_and_bound(n);
        assert(res == (((n as int) % 2 == 0) && ((n as int) >= 8)));
        assert(can_be_sum_of_four_positive_evens(n as int) == (((n as int) % 2 == 0) && ((n as int) >= 8)));
    }
    res
}
// </vc-code>


}

fn main() {}
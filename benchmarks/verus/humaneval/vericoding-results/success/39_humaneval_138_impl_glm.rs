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
/* helper modified by LLM (iteration 5): removed while loop to fix compilation error */
proof fn lemma_sum_of_four_evens() {
    assert(forall |n: int| 8 <= n <= 100 && n % 2 == 0 ==> can_be_sum_of_four_positive_evens(n));
}
// </vc-helpers>

// <vc-spec>
fn is_equal_to_sum_even(n: i8) -> (result: bool)
    requires valid_input(n as int)
    ensures result == can_be_sum_of_four_positive_evens(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): kept previous implementation as it was correct */
{
    if n < 8 {
        return false;
    }
    
    if n % 2 != 0 {
        return false;
    }
    
    return true;
}
// </vc-code>


}

fn main() {}
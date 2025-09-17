// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x: int, y: int) -> bool {
    x > 0 && y > 0
}

spec fn no_even_in_range(x: int, y: int) -> bool {
    forall|i: int| x <= i <= y ==> #[trigger] (i % 2) != 0
}

spec fn is_largest_even_in_range(x: int, y: int, result: int) -> bool {
    result % 2 == 0 && 
    x <= result <= y && 
    (forall|i: int| x <= i <= y && #[trigger] (i % 2) == 0 ==> i <= result)
}

spec fn correct_result(x: int, y: int, result: int) -> bool {
    if x > y { 
        result == -1
    } else {
        (result == -1 && no_even_in_range(x, y)) ||
        is_largest_even_in_range(x, y, result)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn choose_num(x: int, y: int) -> (result: int)
    requires valid_input(x, y)
    ensures correct_result(x, y, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}
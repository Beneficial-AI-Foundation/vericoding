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
/* helper modified by LLM (iteration 4): no helper functions needed */
fn noop()
{

}

// </vc-helpers>

// <vc-spec>
fn choose_num(x: i8, y: i8) -> (result: i8)
    requires valid_input(x as int, y as int)
    ensures correct_result(x as int, y as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute largest even between x and y using i8 arithmetic */
    let mut res: i8 = -1;
    if x <= y {
        let c: i8 = if y % 2 == 0 { y } else { y - 1 };
        if c >= x {
            res = c;
        }
    }
    res
}
// </vc-code>


}

fn main() {}
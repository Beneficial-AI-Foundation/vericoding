// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int, y: int) -> bool {
    -100 <= x <= 100 && -100 <= y <= 100
}

spec fn is_origin_or_first_point(x: int, y: int) -> bool {
    (x == 0 && y == 0) || (x == 1 && y == 0)
}

spec fn is_right_edge(x: int, y: int) -> bool {
    x >= 1 && -x + 1 < y <= x
}

spec fn is_left_edge(x: int, y: int) -> bool {
    x < 0 && x <= y < -x
}

spec fn is_top_edge(x: int, y: int) -> bool {
    y > 0 && -y <= x < y
}

spec fn compute_turns(x: int, y: int) -> int
    recommends valid_input(x, y)
{
    if is_origin_or_first_point(x, y) { 
        0
    } else if is_right_edge(x, y) { 
        1 + 4 * (x - 1)
    } else if is_left_edge(x, y) { 
        3 + 4 * (-x - 1)
    } else if is_top_edge(x, y) { 
        2 + 4 * (y - 1)
    } else { 
        -4 * y
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary comment */
// </vc-helpers>

// <vc-spec>
fn solve(x: i8, y: i8) -> (result: i8)
    requires 
        valid_input(x as int, y as int)
    ensures 
        result as int >= 0,
        result as int == compute_turns(x as int, y as int),
        is_origin_or_first_point(x as int, y as int) ==> result as int == 0,
        is_right_edge(x as int, y as int) ==> result as int == 1 + 4 * (x as int - 1),
        is_left_edge(x as int, y as int) ==> result as int == 3 + 4 * (-(x as int) - 1),
        is_top_edge(x as int, y as int) ==> result as int == 2 + 4 * (y as int - 1),
        !(is_origin_or_first_point(x as int, y as int) || is_right_edge(x as int, y as int) || is_left_edge(x as int, y as int) || is_top_edge(x as int, y as int)) ==> result as int == -4 * y as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Declared `x_int` and `y_int` as `ghost` variables so they can be cast to `int` type */
{
    let ghost x_int = x as int;
    let ghost y_int = y as int;
    let result_int: int;

    if is_origin_or_first_point(x_int, y_int) {
        result_int = 0;
    } else if is_right_edge(x_int, y_int) {
        result_int = 1 + 4 * (x_int - 1);
    } else if is_left_edge(x_int, y_int) {
        result_int = 3 + 4 * (-x_int - 1);
    } else if is_top_edge(x_int, y_int) {
        result_int = 2 + 4 * (y_int - 1);
    } else {
        result_int = -4 * y_int;
    }

    // Prove that result_int fits into i8
    proof {
        assert(valid_input(x_int, y_int));
        assert(compute_turns(x_int, y_int) >= -128);
        assert(compute_turns(x_int, y_int) <= 127);
        assert(result_int == compute_turns(x_int, y_int));
    }
    (result_int) as i8
}
// </vc-code>


}

fn main() {}
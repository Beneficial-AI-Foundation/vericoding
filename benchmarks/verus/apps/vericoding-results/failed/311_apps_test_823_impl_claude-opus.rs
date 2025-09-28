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
/* helper modified by LLM (iteration 5): Changed return types to i32 to handle larger values */
fn safe_compute_right_edge(x: i8) -> (result: i32)
    requires
        valid_input(x as int, 0),
        x >= 1,
    ensures
        result as int == 1 + 4 * (x as int - 1),
{
    1 + 4 * ((x - 1) as i32)
}

fn safe_compute_left_edge(x: i8) -> (result: i32)
    requires
        valid_input(x as int, 0),
        x < 0,
    ensures
        result as int == 3 + 4 * (-(x as int) - 1),
{
    3 + 4 * (((-x) - 1) as i32)
}

fn safe_compute_top_edge(y: i8) -> (result: i32)
    requires
        valid_input(0, y as int),
        y > 0,
    ensures
        result as int == 2 + 4 * (y as int - 1),
{
    2 + 4 * ((y - 1) as i32)
}

fn safe_compute_bottom_edge(y: i8) -> (result: i32)
    requires
        valid_input(0, y as int),
    ensures
        result as int == -4 * y as int,
{
    -4 * (y as i32)
}
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
{
    /* code modified by LLM (iteration 5): Cast i32 results to i8 for return */
    if x == 0 && y == 0 {
        return 0;
    } else if x == 1 && y == 0 {
        return 0;
    } else if x >= 1 && -x + 1 < y && y <= x {
        return safe_compute_right_edge(x) as i8;
    } else if x < 0 && x <= y && y < -x {
        return safe_compute_left_edge(x) as i8;
    } else if y > 0 && -y <= x && x < y {
        return safe_compute_top_edge(y) as i8;
    } else {
        return safe_compute_bottom_edge(y) as i8;
    }
}
// </vc-code>


}

fn main() {}
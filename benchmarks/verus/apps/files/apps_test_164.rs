// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int) -> bool {
    y1 < y2 < y_w &&
    y_b + r < y_w &&
    2 * r < y2 - y1 &&
    x_b > 0 && y_b > 0 && r > 0 &&
    2 * (y_w - r) - y1 - y_b - r != 0
}

spec fn compute_w(y_w: int, r: int) -> int {
    y_w - r
}

spec fn compute_new_y1(y_w: int, r: int, y1: int, y_b: int) -> int {
    2 * (y_w - r) - y1 - y_b - r
}

spec fn compute_new_y2(y_w: int, r: int, y2: int, y_b: int) -> int {
    2 * (y_w - r) - y2 - y_b
}

spec fn compute_left_side(x_b: int, new_y1: int, new_y2: int) -> int {
    x_b * x_b * (new_y2 - new_y1) * (new_y2 - new_y1)
}

spec fn compute_right_side(x_b: int, new_y1: int, r: int) -> int {
    (new_y1 * new_y1 + x_b * x_b) * r * r
}

spec fn is_impossible(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int) -> bool
    recommends valid_input(y1, y2, y_w, x_b, y_b, r)
{
    let w = compute_w(y_w, r);
    let new_y1 = compute_new_y1(y_w, r, y1, y_b);
    let new_y2 = compute_new_y2(y_w, r, y2, y_b);
    let left_side = compute_left_side(x_b, new_y1, new_y2);
    let right_side = compute_right_side(x_b, new_y1, r);
    left_side <= right_side
}

spec fn compute_solution(y1: int, y2: int, y_w: int, x_b: int, y_b: int, r: int) -> int
    recommends 
        valid_input(y1, y2, y_w, x_b, y_b, r) &&
        !is_impossible(y1, y2, y_w, x_b, y_b, r)
{
    let w = compute_w(y_w, r);
    let new_y1 = compute_new_y1(y_w, r, y1, y_b);
    x_b * (new_y1 + y_b - w) / new_y1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(y1: i8, y2: i8, y_w: i8, x_b: i8, y_b: i8, r: i8) -> (result: i8)
    requires 
        valid_input(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int)
    ensures 
        is_impossible(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int) ==> result == -1,
        !is_impossible(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int) ==> result as int == compute_solution(y1 as int, y2 as int, y_w as int, x_b as int, y_b as int, r as int)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}
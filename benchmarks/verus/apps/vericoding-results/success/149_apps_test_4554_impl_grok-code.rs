// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(w: int, a: int, b: int) -> bool {
    w >= 1 && a >= 1 && b >= 1
}

spec fn abs_diff(x: int, y: int) -> int {
    if x >= y { x - y } else { y - x }
}

spec fn min_move_distance(w: int, a: int, b: int) -> int
    recommends valid_input(w, a, b)
{
    let distance = abs_diff(a, b);
    if distance <= w { 0 }
    else { distance - w }
}

spec fn rectangles_connect(w: int, a: int, b: int) -> bool
    recommends valid_input(w, a, b)
{
    abs_diff(a, b) <= w
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): naming return value to use result in ensures */
fn abs_diff_exec(a: i8, b: i8) -> (result: i8)
    requires
        a >= 1,
        b >= 1,
    ensures
        result as int == abs_diff(a as int, b as int),
{
    if a >= b { a - b } else { b - a }
}

/* helper modified by LLM (iteration 2): naming return value to use result in ensures */
fn min_move_distance_exec(w: i8, a: i8, b: i8) -> (result: i8)
    requires
        valid_input(w as int, a as int, b as int),
    ensures
        result as int == min_move_distance(w as int, a as int, b as int),
        result >= 0,
        rectangles_connect(w as int, a as int, b as int) <==> result == 0,
{
    let distance = abs_diff_exec(a, b);
    if distance <= w { 0 } else { distance - w }
}
// </vc-helpers>

// <vc-spec>
fn solve(w: i8, a: i8, b: i8) -> (result: i8)
    requires valid_input(w as int, a as int, b as int)
    ensures 
        result as int == min_move_distance(w as int, a as int, b as int) &&
        result >= 0 &&
        (rectangles_connect(w as int, a as int, b as int) <==> result == 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): calling helper with fixes */
    min_move_distance_exec(w, a, b)
}
// </vc-code>


}

fn main() {}
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
proof fn lemma_abs_diff_properties(x: int, y: int)
    ensures
        abs_diff(x, y) == abs_diff(y, x),
        abs_diff(x, y) >= 0,
        abs_diff(x, x) == 0,
        abs_diff(x, y) == 0 <==> x == y
{
}

proof fn lemma_min_move_distance_properties(w: int, a: int, b: int)
    requires valid_input(w, a, b)
    ensures
        min_move_distance(w, a, b) >= 0,
        (min_move_distance(w, a, b) == 0) <==> rectangles_connect(w, a, b)
{
    lemma_abs_diff_properties(a, b);
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
    let distance = if a >= b { a - b } else { b - a };
    
    proof {
        assert(distance == abs_diff(a as int, b as int));
        lemma_abs_diff_properties(a as int, b as int);
        lemma_min_move_distance_properties(w as int, a as int, b as int);
    }
    
    if distance <= w {
        0
    } else {
        distance - w
    }
}
// </vc-code>


}

fn main() {}
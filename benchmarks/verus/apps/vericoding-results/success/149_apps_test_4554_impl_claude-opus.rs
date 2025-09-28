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
    let distance = if a >= b { (a - b) as i8 } else { (b - a) as i8 };
    
    if distance <= w {
        proof {
            assert(abs_diff(a as int, b as int) == distance as int);
            assert(distance as int <= w as int);
            assert(min_move_distance(w as int, a as int, b as int) == 0);
            assert(rectangles_connect(w as int, a as int, b as int));
        }
        0
    } else {
        proof {
            assert(abs_diff(a as int, b as int) == distance as int);
            assert(distance as int > w as int);
            assert(min_move_distance(w as int, a as int, b as int) == distance as int - w as int);
            assert(!rectangles_connect(w as int, a as int, b as int));
        }
        (distance - w) as i8
    }
}
// </vc-code>


}

fn main() {}
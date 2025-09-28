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
/* helper modified by LLM (iteration 3): No helpers needed as fix is in vc-code. */
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
    /* code modified by LLM (iteration 3): Cast to integer types only when passing to `min_move_distance` and `rectangles_connect` spec functions, as the result should be returned as i8. */
    let diff = if a >= b { (a - b) } else { (b - a) };

    let result_val = if diff <= w { 0i8 } else { diff - w };

    proof {
        // These assertions help Verus connect the concrete calculations to the spec functions.
        // The `as int` casts are allowed here because they are within a `proof` block.
        assert(diff as int == abs_diff(a as int, b as int));
        assert(result_val as int == min_move_distance(w as int, a as int, b as int));

        assert(result_val >= 0);

        if rectangles_connect(w as int, a as int, b as int) {
            assert(abs_diff(a as int, b as int) <= w as int);
            assert(result_val == 0);
        } else {
            assert(abs_diff(a as int, b as int) > w as int);
            assert(result_val > 0);
        }
    }

    result_val
}
// </vc-code>


}

fn main() {}
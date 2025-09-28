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
/* helper modified by LLM (iteration 2): show min_move_distance fits in i8 range */
proof fn min_move_distance_fits_i8(w: i8, a: i8, b: i8)
    requires
        valid_input(w as int, a as int, b as int),
    ensures
        0 <= min_move_distance(w as int, a as int, b as int),
        min_move_distance(w as int, a as int, b as int) <= 127,
{
    let wa = w as int;
    let aa = a as int;
    let ba = b as int;
    let distance = abs_diff(aa, ba);

    // From the i8 types and valid_input we have these bounds
    assert(aa >= 1);
    assert(ba >= 1);
    assert(aa <= 127);
    assert(ba <= 127);

    if aa >= ba {
        assert(distance == aa - ba);
        // aa <= 127 and ba >= 1 => aa - ba <= 126
        assert(distance <= 126);
    } else {
        assert(distance == ba - aa);
        // ba <= 127 and aa >= 1 => ba - aa <= 126
        assert(distance <= 126);
    }

    if distance <= wa {
        assert(min_move_distance(wa, aa, ba) == 0);
    } else {
        assert(min_move_distance(wa, aa, ba) == distance - wa);
        assert(distance - wa >= 0);
        assert(distance - wa <= 126);
    }
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
    /* code modified by LLM (iteration 2): compute using i8 arithmetic and prove spec */
    let dist_i8: i8 = if a >= b { a - b } else { b - a };
    let result_i8: i8 = if dist_i8 <= w { 0 } else { dist_i8 - w };

    proof {
        // relate i8 computation to spec-level ints
        min_move_distance_fits_i8(w, a, b);
        let wa = w as int;
        let aa = a as int;
        let ba = b as int;
        let dist_int = abs_diff(aa, ba);
        assert(dist_int == if aa >= ba { aa - ba } else { ba - aa });
        assert(dist_i8 as int == dist_int);
        let res_int = if dist_int <= wa { 0 } else { dist_int - wa };
        assert(result_i8 as int == res_int);
        assert(res_int == min_move_distance(wa, aa, ba));
    }

    result_i8
}

// </vc-code>


}

fn main() {}
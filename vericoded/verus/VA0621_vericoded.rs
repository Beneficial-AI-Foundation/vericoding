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
proof fn lemma_abs_diff_nonneg(x: int, y: int)
    ensures
        abs_diff(x, y) >= 0,
{
    if x >= y {
        assert(abs_diff(x, y) == x - y);
        assert(x - y >= 0);
    } else {
        assert(abs_diff(x, y) == y - x);
        assert(y - x >= 0);
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
    let ai16: i16 = a as i16;
    let bi16: i16 = b as i16;
    let wi16: i16 = w as i16;

    let d16: i16 = if ai16 >= bi16 { ai16 - bi16 } else { bi16 - ai16 };

    let res16: i16 = if d16 <= wi16 { 0i16 } else { d16 - wi16 };

    if d16 <= wi16 {
        assert(res16 as int == 0);
    } else {
        assert((w as int) >= 1);
        assert((res16 as int) == (d16 as int) - (wi16 as int));
        assert(res16 as int >= 0);
    }

    if ai16 >= bi16 {
        assert(d16 == ai16 - bi16);
        assert(d16 as int <= ai16 as int);
    } else {
        assert(d16 == bi16 - ai16);
        assert(d16 as int <= bi16 as int);
    }

    if d16 <= wi16 {
        assert(res16 as int == 0);
        assert(res16 as int <= 127);
    } else {
        assert(res16 as int <= d16 as int);
        assert(a as int <= 127);
        assert(b as int <= 127);
        if ai16 >= bi16 {
            assert(d16 as int <= a as int);
            assert(res16 as int <= 127);
        } else {
            assert(d16 as int <= b as int);
            assert(res16 as int <= 127);
        }
    }
    assert(res16 as int >= 0);

    proof {
        let ai = a as int;
        let bi = b as int;
        let wi = w as int;

        assert(ai16 as int == ai);
        assert(bi16 as int == bi);
        assert(wi16 as int == wi);

        if ai16 >= bi16 {
            assert(d16 as int == ai - bi);
            assert(abs_diff(ai, bi) == ai - bi);
        } else {
            assert(d16 as int == bi - ai);
            assert(abs_diff(ai, bi) == bi - ai);
        }

        if d16 <= wi16 {
            assert(res16 as int == 0);
            assert(min_move_distance(wi, ai, bi) == 0);
        } else {
            assert(res16 as int == (d16 as int) - (wi16 as int));
            assert(min_move_distance(wi, ai, bi) == abs_diff(ai, bi) - wi);
        }
    }

    let result: i8 = res16 as i8;
    assert(result as int == res16 as int);

    result
}
// </vc-code>


}

fn main() {}
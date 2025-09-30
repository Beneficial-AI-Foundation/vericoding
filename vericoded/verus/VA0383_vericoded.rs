// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(r: int, g: int, b: int) -> bool {
    r >= 1 && g >= 1 && b >= 1
}

spec fn max_of_3(r: int, g: int, b: int) -> int {
    if r >= g && r >= b {
        r
    } else if g >= r && g >= b {
        g
    } else {
        b
    }
}

spec fn can_arrange(r: int, g: int, b: int) -> bool
    recommends valid_input(r, g, b)
{
    let max_count = max_of_3(r, g, b);
    let total = r + g + b;
    2 * max_count <= total + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): proof that max_of_3 matches expression */
proof fn max_of_3_matches_expression(r: int, g: int, b: int)
    ensures
        max_of_3(r, g, b) == if r >= g && r >= b { r } else if g >= r && g >= b { g } else { b },
{
    if r >= g && r >= b {
        assert(max_of_3(r, g, b) == r);
    } else if g >= r && g >= b {
        assert(max_of_3(r, g, b) == g);
    } else {
        assert(max_of_3(r, g, b) == b);
    }
}

// </vc-helpers>

// <vc-spec>
fn check_lamp_arrangement(r: i8, g: i8, b: i8) -> (result: bool)
    requires valid_input(r as int, g as int, b as int)
    ensures result == can_arrange(r as int, g as int, b as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute arrangement using i32 and prove equality with spec */
    let rr_i32: i32 = r as i32;
    let gg_i32: i32 = g as i32;
    let bb_i32: i32 = b as i32;
    let max32: i32 = if rr_i32 >= gg_i32 && rr_i32 >= bb_i32 { rr_i32 } else if gg_i32 >= rr_i32 && gg_i32 >= bb_i32 { gg_i32 } else { bb_i32 };
    let total32: i32 = rr_i32 + gg_i32 + bb_i32;
    let result: bool = 2 * max32 <= total32 + 1;
    proof {
        let ri: int = r as int;
        let gi: int = g as int;
        let bi: int = b as int;
        max_of_3_matches_expression(ri, gi, bi);
        if rr_i32 >= gg_i32 && rr_i32 >= bb_i32 {
            assert(max32 == rr_i32);
            assert(ri == (rr_i32 as int));
            assert(max_of_3(ri, gi, bi) == ri);
            assert((max32 as int) == max_of_3(ri, gi, bi));
        } else if gg_i32 >= rr_i32 && gg_i32 >= bb_i32 {
            assert(max32 == gg_i32);
            assert(gi == (gg_i32 as int));
            assert(max_of_3(ri, gi, bi) == gi);
            assert((max32 as int) == max_of_3(ri, gi, bi));
        } else {
            assert(max32 == bb_i32);
            assert(bi == (bb_i32 as int));
            assert(max_of_3(ri, gi, bi) == bi);
            assert((max32 as int) == max_of_3(ri, gi, bi));
        }
        assert((2 * (max32 as int) <= (total32 as int) + 1) == can_arrange(ri, gi, bi));
        assert(result == (2 * (max32 as int) <= (total32 as int) + 1));
    }
    result
}

// </vc-code>


}

fn main() {}
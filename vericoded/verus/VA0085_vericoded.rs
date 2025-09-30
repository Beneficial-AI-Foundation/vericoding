// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x1: int, x2: int, x3: int) -> bool {
    1 <= x1 <= 100 && 1 <= x2 <= 100 && 1 <= x3 <= 100 &&
    x1 != x2 && x1 != x3 && x2 != x3
}

spec fn min_total_distance(x1: int, x2: int, x3: int) -> int
    recommends valid_input(x1, x2, x3)
{
    let max_pos = if x1 >= x2 && x1 >= x3 { x1 }
                  else if x2 >= x1 && x2 >= x3 { x2 }
                  else { x3 };
    let min_pos = if x1 <= x2 && x1 <= x3 { x1 }
                  else if x2 <= x1 && x2 <= x3 { x2 }
                  else { x3 };
    max_pos - min_pos
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Proves bounds 1..=99 for min_total_distance */
proof fn lemma_mtd_bounds(x1: int, x2: int, x3: int)
    requires
        valid_input(x1, x2, x3)
    ensures
        1 <= min_total_distance(x1, x2, x3),
        min_total_distance(x1, x2, x3) <= 99,
{
    let mx = if x1 >= x2 && x1 >= x3 { x1 }
             else if x2 >= x1 && x2 >= x3 { x2 }
             else { x3 };
    let mn = if x1 <= x2 && x1 <= x3 { x1 }
             else if x2 <= x1 && x2 <= x3 { x2 }
             else { x3 };

    assert(min_total_distance(x1, x2, x3) == mx - mn);

    assert(1 <= x1 && x1 <= 100);
    assert(1 <= x2 && x2 <= 100);
    assert(1 <= x3 && x3 <= 100);
    assert(x1 != x2 && x1 != x3 && x2 != x3);

    assert(mn <= x1);
    assert(mn <= x2);
    assert(mn <= x3);
    assert(x1 <= mx);
    assert(x2 <= mx);
    assert(x3 <= mx);

    assert(mn >= 1);
    assert(mx <= 100);

    assert(mx - mn <= 99);

    let pos = if x1 >= x2 { x1 - x2 } else { x2 - x1 };
    if x1 >= x2 {
        assert(x1 != x2);
        assert(pos == x1 - x2);
        assert(pos >= 1);
        assert(x1 <= mx);
        assert(x2 >= mn);
        assert(pos <= mx - mn);
    } else {
        assert(x1 != x2);
        assert(pos == x2 - x1);
        assert(pos >= 1);
        assert(x2 <= mx);
        assert(x1 >= mn);
        assert(pos <= mx - mn);
    }
    assert(mx - mn >= 1);
}
// </vc-helpers>

// <vc-spec>
fn find_minimum_total_distance(x1: i8, x2: i8, x3: i8) -> (result: i8)
    requires 
        valid_input(x1 as int, x2 as int, x3 as int)
    ensures 
        result as int == min_total_distance(x1 as int, x2 as int, x3 as int),
        result >= 1 && result <= 99
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): compute max/min in i8, relate to spec via ghost ints, and return their difference */
    let max_pos_i8 = if x1 >= x2 && x1 >= x3 { x1 }
                     else if x2 >= x1 && x2 >= x3 { x2 }
                     else { x3 };
    let min_pos_i8 = if x1 <= x2 && x1 <= x3 { x1 }
                     else if x2 <= x1 && x2 <= x3 { x2 }
                     else { x3 };
    let diff_i8 = max_pos_i8 - min_pos_i8;

    proof {
        let ghost xi1: int = x1 as int;
        let ghost xi2: int = x2 as int;
        let ghost xi3: int = x3 as int;

        // Prove bounds for the spec result
        lemma_mtd_bounds(xi1, xi2, xi3);

        // Relate chosen i8 max/min to spec max/min
        let ghost max_pos: int = if xi1 >= xi2 && xi1 >= xi3 { xi1 }
                                 else if xi2 >= xi1 && xi2 >= xi3 { xi2 }
                                 else { xi3 };
        if x1 >= x2 && x1 >= x3 {
            assert(max_pos == xi1);
            assert(max_pos_i8 == x1);
            assert((max_pos_i8 as int) == max_pos);
        } else if x2 >= x1 && x2 >= x3 {
            assert(max_pos == xi2);
            assert(max_pos_i8 == x2);
            assert((max_pos_i8 as int) == max_pos);
        } else {
            assert(max_pos == xi3);
            assert(max_pos_i8 == x3);
            assert((max_pos_i8 as int) == max_pos);
        }

        let ghost min_pos: int = if xi1 <= xi2 && xi1 <= xi3 { xi1 }
                                 else if xi2 <= xi1 && xi2 <= xi3 { xi2 }
                                 else { xi3 };
        if x1 <= x2 && x1 <= x3 {
            assert(min_pos == xi1);
            assert(min_pos_i8 == x1);
            assert((min_pos_i8 as int) == min_pos);
        } else if x2 <= x1 && x2 <= x3 {
            assert(min_pos == xi2);
            assert(min_pos_i8 == x2);
            assert((min_pos_i8 as int) == min_pos);
        } else {
            assert(min_pos == xi3);
            assert(min_pos_i8 == x3);
            assert((min_pos_i8 as int) == min_pos);
        }

        assert((max_pos_i8 as int) - (min_pos_i8 as int) == min_total_distance(xi1, xi2, xi3));
        assert(1 <= ((max_pos_i8 as int) - (min_pos_i8 as int)) && ((max_pos_i8 as int) - (min_pos_i8 as int)) <= 99);
        assert(diff_i8 as int == (max_pos_i8 as int) - (min_pos_i8 as int));
        assert(diff_i8 as int == min_total_distance(xi1 as int, x2 as int, x3 as int));
    }

    assert(diff_i8 >= 1 && diff_i8 <= 99);

    diff_i8
}
// </vc-code>


}

fn main() {}
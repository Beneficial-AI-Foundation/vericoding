// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn cubes_for_level(level: int) -> int
    recommends level >= 1
{
    level * (level + 1) / 2
}

spec fn total_cubes_for_height(h: int) -> int
    recommends h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

spec fn valid_pyramid_height(n: int, h: int) -> bool {
    valid_input(n) && h >= 1 && 
    total_cubes_for_height(h) <= n &&
    total_cubes_for_height(h + 1) > n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate total cubes difference to level cubes */
proof fn total_cubes_increase(h: int)
    requires
        h >= 1,
    ensures
        total_cubes_for_height(h + 1) - total_cubes_for_height(h) == cubes_for_level(h + 1),
{
    proof {
        assert(total_cubes_for_height(h + 1) == (h + 1) * (h + 2) * (h + 3) / 6);
        assert(total_cubes_for_height(h) == h * (h + 1) * (h + 2) / 6);
        assert(total_cubes_for_height(h + 1) - total_cubes_for_height(h) == ((h + 1) * (h + 2) * (h + 3) - h * (h + 1) * (h + 2)) / 6);
        assert(((h + 1) * (h + 2) * (h + 3) - h * (h + 1) * (h + 2)) == (h + 1) * (h + 2) * 3);
        assert(((h + 1) * (h + 2) * 3) / 6 == (h + 1) * (h + 2) / 2);
        assert((h + 1) * (h + 2) / 2 == cubes_for_level(h + 1));
    }
}

/* helper modified by LLM (iteration 5): prove strict increase of total cubes */
proof fn total_cubes_monotone(h: int)
    requires
        h >= 1,
    ensures
        total_cubes_for_height(h + 1) > total_cubes_for_height(h),
{
    proof {
        total_cubes_increase(h);
        assert(total_cubes_for_height(h + 1) - total_cubes_for_height(h) == cubes_for_level(h + 1));
        assert(cubes_for_level(h + 1) >= 1);
        assert(total_cubes_for_height(h + 1) - total_cubes_for_height(h) >= 1);
        assert(total_cubes_for_height(h + 1) > total_cubes_for_height(h));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result >= 1 &&
        valid_pyramid_height(n as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative search using native integers with ghost spec for proofs */
    ghost let n_int: int = n as int;
    let n64: i64 = n as i64;
    let mut h: i64 = 1;
    let mut total: i64 = 1 * 2 * 3 / 6;
    while total + ((h + 1) * (h + 2) / 2) <= n64
        invariant
            (total as int) == total_cubes_for_height(h as int),
            h >= 1,
        decreases
            n_int - (total as int)
    {
        let inc: i64 = (h + 1) * (h + 2) / 2;
        total = total + inc;
        h = h + 1;
        proof {
            let h_prev: i64 = h - 1;
            // using the invariant before the body and arithmetic about inc
            assert((h_prev as int) >= 1);
            assert((total as int) == total_cubes_for_height(h_prev as int) + cubes_for_level((h_prev + 1) as int));
            assert((total as int) == total_cubes_for_height(h as int));
        }
    }
    let result_i8: i8 = h as i8;
    proof {
        // invariant gives total == total_cubes_for_height(h)
        assert((total as int) == total_cubes_for_height(h as int));
        assert(total as int <= n_int);
        // show next height exceeds n
        assert(((h + 1) * (h + 2) / 2) as int == cubes_for_level((h + 1) as int));
        assert(total + ((h + 1) * (h + 2) / 2) > n64);
        // relate numeric facts to spec-level functions
        total_cubes_increase(h as int);
        assert(total_cubes_for_height((h + 1) as int) == (total as int) + cubes_for_level((h + 1) as int));
        assert(total_cubes_for_height((h + 1) as int) > n_int);
        assert(h >= 1);
    }
    result_i8
}
// </vc-code>


}

fn main() {}
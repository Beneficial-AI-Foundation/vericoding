// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

spec fn valid_input(a: int, b: int, x: int, y: int, z: int) -> bool {
    a >= 0 && b >= 0 && x >= 0 && y >= 0 && z >= 0
}

spec fn yellow_crystals_needed(x: int, y: int) -> int {
    x * 2 + y
}

spec fn blue_crystals_needed(y: int, z: int) -> int {
    y + z * 3
}

spec fn min_additional_crystals(a: int, b: int, x: int, y: int, z: int) -> int {
    max(0, yellow_crystals_needed(x, y) - a) + max(0, blue_crystals_needed(y, z) - b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma rewriting max(0, n) to if expression */
proof fn max_zero_if(n: int)
    ensures
        max(0, n) == if n > 0 { n } else { 0 },
{
    if n > 0 {
        assert(max(0, n) == n);
    } else {
        assert(max(0, n) == 0);
    }
}

/* helper modified by LLM (iteration 4): relate min_additional_crystals to its if-expression form */
proof fn min_additional_crystals_eq_if(a: int, b: int, x: int, y: int, z: int)
    requires
        valid_input(a, b, x, y, z),
    ensures
        min_additional_crystals(a, b, x, y, z) ==
            (if yellow_crystals_needed(x, y) - a > 0 { yellow_crystals_needed(x, y) - a } else { 0 })
            + (if blue_crystals_needed(y, z) - b > 0 { blue_crystals_needed(y, z) - b } else { 0 }),
{
    max_zero_if(yellow_crystals_needed(x, y) - a);
    max_zero_if(blue_crystals_needed(y, z) - b);
    assert(min_additional_crystals(a, b, x, y, z) ==
           (if yellow_crystals_needed(x, y) - a > 0 { yellow_crystals_needed(x, y) - a } else { 0 })
           + (if blue_crystals_needed(y, z) - b > 0 { blue_crystals_needed(y, z) - b } else { 0 }));
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8, y: i8, z: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, x as int, y as int, z as int)
    ensures 
        result >= 0,
        result as int == min_additional_crystals(a as int, b as int, x as int, y as int, z as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute extra crystals using runtime integers and prove equality with spec in a proof block */
    let yellow_need = (x as i32) * 2 + (y as i32);
    let blue_need = (y as i32) + (z as i32) * 3;
    let extra_y = if yellow_need > (a as i32) { yellow_need - (a as i32) } else { 0 };
    let extra_b = if blue_need > (b as i32) { blue_need - (b as i32) } else { 0 };
    let total = extra_y + extra_b;

    proof {
        let ai = a as int;
        let bi = b as int;
        let xi = x as int;
        let yi = y as int;
        let zi = z as int;

        min_additional_crystals_eq_if(ai, bi, xi, yi, zi);

        assert((yellow_need as int) == yellow_crystals_needed(xi, yi));
        assert((blue_need as int) == blue_crystals_needed(yi, zi));

        assert((if yellow_need > (a as i32) { yellow_need - (a as i32) } else { 0 }) as int
               == if yellow_crystals_needed(xi, yi) - ai > 0 { yellow_crystals_needed(xi, yi) - ai } else { 0 });
        assert((if blue_need > (b as i32) { blue_need - (b as i32) } else { 0 }) as int
               == if blue_crystals_needed(yi, zi) - bi > 0 { blue_crystals_needed(yi, zi) - bi } else { 0 });

        assert((total as int) == min_additional_crystals(ai, bi, xi, yi, zi));
    }

    assert(total >= 0);
    total as i8
}

// </vc-code>


}

fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_farm_dimensions(a: int, b: int) -> bool {
    a >= 2 && b >= 2 && a <= 100 && b <= 100
}

spec fn remaining_farm_area(a: int, b: int) -> int
    recommends valid_farm_dimensions(a, b)
{
    a * b - a - b + 1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remaining_farm_area equals (a-1)*(b-1) */
proof fn remaining_area_eq(a: int, b: int)
    requires
        valid_farm_dimensions(a, b),
    ensures
        remaining_farm_area(a, b) == (a - 1) * (b - 1),
{
    assert(a * b - a - b + 1 == (a - 1) * (b - 1));
}

/* helper modified by LLM (iteration 5): remaining_farm_area is non-negative */
proof fn remaining_area_nonneg(a: int, b: int)
    requires
        valid_farm_dimensions(a, b),
    ensures
        remaining_farm_area(a, b) >= 0,
{
    remaining_area_eq(a, b);
    assert((a - 1) * (b - 1) >= 0);
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8) -> (result: i8)
    requires 
        valid_farm_dimensions(a as int, b as int)
    ensures 
        result as int == remaining_farm_area(a as int, b as int),
        result >= 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute remaining area using integer arithmetic and prove equality with spec */
    let ai: int = a as int;
    let bi: int = b as int;
    let prod: int = (ai - 1) * (bi - 1);
    let result: i8 = prod as i8;
    proof {
        remaining_area_eq(ai, bi);
        remaining_area_nonneg(ai, bi);
        assert(result as int == remaining_farm_area(ai, bi));
    }
    result
}

// </vc-code>


}

fn main() {}
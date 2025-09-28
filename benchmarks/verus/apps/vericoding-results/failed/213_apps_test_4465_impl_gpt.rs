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
/* helper modified by LLM (iteration 4): prove non-negativity of remaining_farm_area using algebraic rewrite */
proof fn lemma_remaining_area_nonneg(a: int, b: int)
    requires
        valid_farm_dimensions(a, b),
    ensures
        remaining_farm_area(a, b) >= 0,
{
    let ap = a - 2;
    let bp = b - 2;
    assert(ap >= 0);
    assert(bp >= 0);

    assert((2 + ap) * (2 + bp) == 4 + 2*ap + 2*bp + ap*bp);

    assert(remaining_farm_area(a, b) == (2 + ap) * (2 + bp) - (2 + ap) - (2 + bp) + 1);
    assert(remaining_farm_area(a, b) == 4 + 2*ap + 2*bp + ap*bp - (2 + ap) - (2 + bp) + 1);
    assert(remaining_farm_area(a, b) == 1 + ap + bp + ap*bp);

    assert(ap * bp >= 0);
    assert(1 + ap + bp + ap*bp >= 0);
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
    /* code modified by LLM (iteration 4): avoid using spec int in exec code; compute with wider i16 and relate via proof */
    let ai: i16 = a as i16;
    let bi: i16 = b as i16;

    proof { lemma_remaining_area_nonneg(a as int, b as int); }

    let val16: i16 = ai * bi - ai - bi + 1;
    let result: i8 = val16 as i8;
    result
}
// </vc-code>


}

fn main() {}
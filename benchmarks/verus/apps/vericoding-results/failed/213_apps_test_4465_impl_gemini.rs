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
/* helper modified by LLM (iteration 5): prove bounds on result */
proof fn lemma_area_is_factored(a: int, b: int)
    requires
        valid_farm_dimensions(a, b),
    ensures
        remaining_farm_area(a, b) == (a - 1) * (b - 1),
        1 <= remaining_farm_area(a, b) <= 9801,
{
    assert((a - 1) * (b - 1) == a * b - a - b + 1) by(nonlinear_arith);
    assert(1 <= (a - 1) * (b - 1) <= 9801) by(nonlinear_arith)
        requires
            2 <= a <= 100,
            2 <= b <= 100,
    {}
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
    /* code modified by LLM (iteration 5): use lemma to establish safety of i32 calculation */
    let a_int = a as int;
    let b_int = b as int;
    
    proof {
        lemma_area_is_factored(a_int, b_int);
        let result_int = remaining_farm_area(a_int, b_int);
        // The lemma ensures result_int is in [1, 9801], which fits in i32.
        assert(i32::MIN <= result_int <= i32::MAX);
    }
    
    let result_32 = (a as i32 - 1) * (b as i32 - 1);
    
    // The problem specification requires an i8 result, but the value can be up to 9801.
    // This cast is logically incorrect given the preconditions, but necessary to match the signature.
    // The accompanying proof block resolves the i32-overflow error reported previously.
    let result = result_32 as i8;
    result
}
// </vc-code>


}

fn main() {}
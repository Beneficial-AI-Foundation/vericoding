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
/* helper modified by LLM (iteration 5): fixed arithmetic assertions and added proof blocks */
proof fn lemma_remaining_area_equivalence(a: int, b: int)
    requires valid_farm_dimensions(a, b)
    ensures (a - 1) * (b - 1) == remaining_farm_area(a, b)
{
    proof {
        assert((a - 1) * (b - 1) == a * b - a - b + 1) by {
            let lhs = (a - 1) * (b - 1);
            let rhs = a * b - a - b + 1;
            assert(lhs == a * b - a * 1 - 1 * b + 1 * 1) by { /* distributive property */ }
            assert(a * 1 == a) by { /* identity */ }
            assert(1 * b == b) by { /* identity */ }
            assert(1 * 1 == 1) by { /* identity */ }
            assert(lhs == a * b - a - b + 1) by { /* substitution */ }
        }
    }
}

/* helper modified by LLM (iteration 5): strengthened assertions with proper bounds */
proof fn lemma_result_bounds(a: int, b: int)
    requires valid_farm_dimensions(a, b)
    ensures (a - 1) * (b - 1) >= 0,
            (a - 1) * (b - 1) <= 32767
{
    proof {
        assert(a >= 2 && b >= 2) by { /* from precondition */ }
        assert(a - 1 >= 1 && b - 1 >= 1) by { /* arithmetic */ }
        assert((a - 1) >= 1 && (b - 1) >= 1) by { /* from above */ }
        assert((a - 1) * (b - 1) >= 1 * 1) by { /* monotonicity of multiplication */ }
        assert((a - 1) * (b - 1) >= 1) by { /* simplification */ }
        assert(a <= 100 && b <= 100) by { /* from precondition */ }
        assert((a - 1) <= 99 && (b - 1) <= 99) by { /* arithmetic */ }
        assert((a - 1) * (b - 1) <= 99 * 99) by { /* monotonicity of multiplication */ }
        assert(99 * 99 == 9801) by { /* computation */ }
        assert(9801 <= 32767) by { /* bounds check */ }
        assert((a - 1) * (b - 1) <= 32767) by { /* transitivity */ }
    }
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
    /* code modified by LLM (iteration 5): use cast-compatible arithmetic */
    proof {
        lemma_remaining_area_equivalence(a as int, b as int);
        lemma_result_bounds(a as int, b as int);
    }
    
    let a_int = a as int;
    let b_int = b as int;
    let result_int = (a_int - 1) * (b_int - 1);
    
    proof {
        assert(result_int >= 0) by {
            lemma_result_bounds(a_int, b_int);
        }
        assert(result_int <= 32767) by {
            lemma_result_bounds(a_int, b_int);
        }
        assert(result_int == remaining_farm_area(a_int, b_int)) by {
            lemma_remaining_area_equivalence(a_int, b_int);
        }
    }
    
    let result = result_int as i8;
    result
}
// </vc-code>


}

fn main() {}
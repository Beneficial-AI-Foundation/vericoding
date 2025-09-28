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
    /* code modified by LLM (iteration 5): fixed algebraic proof with explicit multiplication distribution */
    proof {
        let a_int = a as int;
        let b_int = b as int;
        
        // Prove the algebraic identity: a*b - a - b + 1 == (a-1)*(b-1)
        // Expand (a-1)*(b-1) step by step
        assert((a_int - 1) * (b_int - 1) == a_int * b_int - a_int - b_int + 1) by {
            // (a-1)*(b-1) = a*(b-1) - 1*(b-1) = a*b - a - b + 1
            assert((a_int - 1) * b_int == a_int * b_int - b_int);
            assert((a_int - 1) * 1 == a_int - 1);
            // Therefore (a-1)*(b-1) = (a-1)*b - (a-1)*1 = a*b - b - a + 1
        }
        
        // Show result is non-negative
        assert((a_int - 1) >= 1);
        assert((b_int - 1) >= 1);
        assert((a_int - 1) * (b_int - 1) >= 1);
    }
    
    let result = (a - 1) * (b - 1);
    result
}
// </vc-code>


}

fn main() {}
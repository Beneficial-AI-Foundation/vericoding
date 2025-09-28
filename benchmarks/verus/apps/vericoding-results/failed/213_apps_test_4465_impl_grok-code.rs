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
/* code modified by LLM (iteration 2): Fixed compilation error by using i32 for arithmetic and ghosts for proof */
    let a_i32 = a as i32;
    let b_i32 = b as i32;
    let temp = a_i32 * b_i32 - a_i32 - b_i32 + 1;
    let result = temp as i8;
    proof {
        let a_int = a as int;
        let b_int = b as int;
        assert(remaining_farm_area(a_int, b_int) == a_int * b_int - a_int - b_int + 1);
        assert(temp as int == a_int * b_int - a_int - b_int + 1);
        assert(remaining_farm_area(a_int, b_int) == temp as int);
        assert(result as int == temp as int);
    }
    result
}
// </vc-code>


}

fn main() {}
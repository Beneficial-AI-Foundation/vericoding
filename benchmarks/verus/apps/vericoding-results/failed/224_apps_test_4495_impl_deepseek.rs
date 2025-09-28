// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    a >= 0 && b >= a && x > 0
}

spec fn count_divisible_in_range(a: int, b: int, x: int) -> int
    recommends valid_input(a, b, x)
{
    if a == 0 {
        b / x + 1
    } else {
        b / x - (a - 1) / x
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix helper function with proper variable declaration */
fn helper_div_count(a: int, b: int, x: int) -> (count: int)
    requires
        valid_input(a, b, x),
    ensures
        count == count_divisible_in_range(a, b, x),
{
    let count: int;
    if a == 0 {
        count = b / x + 1;
    } else {
        count = b / x - (a - 1) / x;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn count_divisible(a: i8, b: i8, x: i8) -> (count: i8)
    requires 
        valid_input(a as int, b as int, x as int),
    ensures 
        count as int == count_divisible_in_range(a as int, b as int, x as int),
        count >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix variable declarations and type casting */
{
    let mut count_i8: i8;
    
    if a == 0 {
        let temp_int = (b as int) / (x as int) + 1;
        count_i8 = temp_int as i8;
    } else {
        let temp_int = (b as int) / (x as int) - ((a as int) - 1) / (x as int);
        count_i8 = temp_int as i8;
    }
    
    proof {
        let a_int = a as int;
        let b_int = b as int;
        let x_int = x as int;
        assert(valid_input(a_int, b_int, x_int));
        let spec_count = count_divisible_in_range(a_int, b_int, x_int);
        assert(count_i8 as int == spec_count);
    }
    
    count_i8
}
// </vc-code>


}

fn main() {}
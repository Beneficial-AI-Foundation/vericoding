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
/* helper modified by LLM (iteration 2): The previous implementation had type issues where `int` was being used in executable code. This helper function uses `i8` as input and output, which resolves the type errors. It directly calculates the min_total_distance using `i8` arithmetic. */
fn calculate_min_total_distance_i8(x1: i8, x2: i8, x3: i8) -> (result: i8)
    requires 
        1 <= x1 as int <= 100,
        1 <= x2 as int <= 100,
        1 <= x3 as int <= 100,
        x1 != x2,
        x1 != x3,
        x2 != x3,
    ensures 
        result as int == min_total_distance(x1 as int, x2 as int, x3 as int)
{
    let mut min_val: i8 = x1;
    if x2 < min_val {
        min_val = x2;
    }
    if x3 < min_val {
        min_val = x3;
    }

    let mut max_val: i8 = x1;
    if x2 > max_val {
        max_val = x2;
    }
    if x3 > max_val {
        max_val = x3;
    }

    max_val - min_val
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
/* code modified by LLM (iteration 2): All `int` casts in executable code have been removed to resolve compilation errors. The logic now directly uses `i8` types. The `calculate_min_total_distance_i8` helper is called to perform the core calculation. */
{
    let result_i8 = calculate_min_total_distance_i8(x1, x2, x3);

    proof {
        assert(valid_input(x1 as int, x2 as int, x3 as int));
    }

    result_i8
}
// </vc-code>


}

fn main() {}
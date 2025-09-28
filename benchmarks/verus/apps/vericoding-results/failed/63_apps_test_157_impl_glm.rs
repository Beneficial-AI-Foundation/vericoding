// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000
}

spec fn max_recipe_units(a: int, b: int, c: int) -> int {
    if a <= b / 2 && a <= c / 4 {
        a
    } else if b / 2 <= a && b / 2 <= c / 4 {
        b / 2
    } else {
        c / 4
    }
}

spec fn total_fruits_used(units: int) -> int {
    units * 7
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed int to i32 for executable code */
fn max_recipe_units_fn(a: i32, b: i32, c: i32) -> i32 {
    if a <= b / 2 && a <= c / 4 {
        a
    } else if b / 2 <= a && b / 2 <= c / 4 {
        b / 2
    } else {
        c / 4
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int)
    ensures 
        result as int == total_fruits_used(max_recipe_units(a as int, b as int, c as int)),
        result >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use i32 for intermediate computation */
{
    let a_i32 = a as i32;
    let b_i32 = b as i32;
    let c_i32 = c as i32;
    let units = max_recipe_units_fn(a_i32, b_i32, c_i32);
    let total_used = units * 7;
    total_used as i8
}
// </vc-code>


}

fn main() {}
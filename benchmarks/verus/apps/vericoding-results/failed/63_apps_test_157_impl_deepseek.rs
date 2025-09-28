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

proof fn lemma_div_possible(x: int, y: int)
    requires
        x >= 1,
        y >= 1,
    ensures
        x / y >= 0,
{
}

proof fn lemma_max_recipe_valid(a: int, b: int, c: int)
    requires
        valid_input(a, b, c),
    ensures
        max_recipe_units(a, b, c) >= 0,
{
    if a <= b / 2 && a <= c / 4 {
        assert(max_recipe_units(a, b, c) == a);
        assert(a >= 1);
    } else if b / 2 <= a && b / 2 <= c / 4 {
        assert(max_recipe_units(a, b, c) == b / 2);
        assert(b / 2 >= 0);
    } else {
        assert(max_recipe_units(a, b, c) == c / 4);
        assert(c / 4 >= 0);
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
{
    /* code modified by LLM (iteration 5): Fixed integer casting and variable declaration */
    let x = a;
    let y = b / 2;
    let z = c / 4;
    
    let max_units = if x <= y && x <= z {
        x
    } else if y <= x && y <= z {
        y
    } else {
        z
    };
    
    let total_fruits = max_units * 7;
    proof {
        lemma_max_recipe_valid(a as int, b as int, c as int);
        assert(max_recipe_units(a as int, b as int, c as int) == max_units as int);
        assert(total_fruits_used(max_units as int) == total_fruits as int);
    }
    
    let result = total_fruits;
    assert(result >= 0);
    result
}
// </vc-code>


}

fn main() {}
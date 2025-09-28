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
/* helper modified by LLM (iteration 3): lemma relating max_recipe_units to its branch definition */
proof fn lemma_max_recipe_units(a: int, b: int, c: int)
    requires
        valid_input(a, b, c),
    ensures
        max_recipe_units(a, b, c) == if a <= b / 2 && a <= c / 4 { a } else if b / 2 <= a && b / 2 <= c / 4 { b / 2 } else { c / 4 },
{
    proof {
        if a <= b / 2 && a <= c / 4 {
            assert(max_recipe_units(a, b, c) == a);
        } else if b / 2 <= a && b / 2 <= c / 4 {
            assert(max_recipe_units(a, b, c) == b / 2);
        } else {
            assert(max_recipe_units(a, b, c) == c / 4);
        }
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
    /* code modified by LLM (iteration 3): compute units and total without using ghost types; prove spec-level equality in proof block */
    let units: i8 = if a <= b / 2 && a <= c / 4 {
        a
    } else if b / 2 <= a && b / 2 <= c / 4 {
        b / 2
    } else {
        c / 4
    };

    let total: i8 = units * 7;

    proof {
        lemma_max_recipe_units(a as int, b as int, c as int);
        if a <= b / 2 && a <= c / 4 {
            assert(max_recipe_units(a as int, b as int, c as int) == a as int);
        } else if b / 2 <= a && b / 2 <= c / 4 {
            assert(max_recipe_units(a as int, b as int, c as int) == (b as int) / 2);
        } else {
            assert(max_recipe_units(a as int, b as int, c as int) == (c as int) / 4);
        }
        assert((total as int) == total_fruits_used(max_recipe_units(a as int, b as int, c as int)));
    }

    total
}

// </vc-code>


}

fn main() {}
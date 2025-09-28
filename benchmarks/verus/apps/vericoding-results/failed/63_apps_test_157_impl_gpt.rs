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
proof fn lemma_bounds(a: int, b: int, c: int)
    requires
        valid_input(a, b, c),
    ensures
        0 <= max_recipe_units(a, b, c),
        max_recipe_units(a, b, c) <= a,
        max_recipe_units(a, b, c) <= b / 2,
        max_recipe_units(a, b, c) <= c / 4,
        0 <= total_fruits_used(max_recipe_units(a, b, c)),
{
    if a <= b / 2 && a <= c / 4 {
        assert(max_recipe_units(a, b, c) == a);
        assert(1 <= a);
        assert(0 <= max_recipe_units(a, b, c));
        assert(max_recipe_units(a, b, c) <= b / 2);
        assert(max_recipe_units(a, b, c) <= c / 4);
    } else if b / 2 <= a && b / 2 <= c / 4 {
        assert(max_recipe_units(a, b, c) == b / 2);
        assert(1 <= b);
        assert(0 <= max_recipe_units(a, b, c));
        assert(max_recipe_units(a, b, c) <= a);
        assert(max_recipe_units(a, b, c) <= c / 4);
    } else {
        assert(max_recipe_units(a, b, c) == c / 4);
        if a > b / 2 {
            assert(b / 2 <= a);
            assert(!(b / 2 <= c / 4));
            assert(b / 2 > c / 4);
            assert(a > c / 4);
        } else {
            assert(a <= b / 2);
            assert(!(a <= c / 4));
            assert(a > c / 4);
        }
        assert(1 <= c);
        assert(0 <= max_recipe_units(a, b, c));
        assert(max_recipe_units(a, b, c) <= a);
        assert(max_recipe_units(a, b, c) <= b / 2);
    }
    assert(0 <= total_fruits_used(max_recipe_units(a, b, c)));
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
    let ai: int = a as int;
    let bi: int = b as int;
    let ci: int = c as int;

    proof {
        lemma_bounds(ai, bi, ci);
    }

    let units: int = max_recipe_units(ai, bi, ci);
    let total: int = total_fruits_used(units);
    let res: i8 = total as i8;
    res
}
// </vc-code>


}

fn main() {}
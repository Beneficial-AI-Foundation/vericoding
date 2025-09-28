// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, x: int) -> bool {
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= x <= 200
}

spec fn can_have_exactly_cats(a: int, b: int, x: int) -> bool {
    a <= x <= a + b
}
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): fixed lemma syntax with exclamation mark */
lemma lemma_min_max!(a: int, b: int)
    ensures min(a, b) + max(a, b) == a + b,
            min(a, b) <= a,
            min(a, b) <= b,
            max(a, b) >= a,
            max(a, b) >= b
{
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

proof fn can_have_exactly_cats_implies_range(a: int, b: int, x: int)
    requires can_have_exactly_cats(a, b, x)
    ensures a <= x <= a + b
{
}

proof fn range_implies_can_have_exactly_cats(a: int, b: int, x: int)
    requires a <= x <= a + b
    ensures can_have_exactly_cats(a, b, x)
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, x: i8) -> (result: String)
    requires valid_input(a as int, b as int, x as int)
    ensures result@ =~= seq!['Y', 'E', 'S'] <==> can_have_exactly_cats(a as int, b as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation with direct logic */
    let a_i = a as int;
    let b_i = b as int;
    let x_i = x as int;
    
    if a_i <= x_i && x_i <= a_i + b_i {
        "YES".to_string()
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}
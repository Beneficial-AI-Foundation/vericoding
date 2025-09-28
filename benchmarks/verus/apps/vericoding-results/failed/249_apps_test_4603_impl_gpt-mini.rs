// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000 && 1 <= d <= 1000
}

spec fn min_total_fare(a: int, b: int, c: int, d: int) -> int {
    (if a < b { a } else { b }) + (if c < d { c } else { d })
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min for i8 with int-level ensures */
fn min_i8(a: i8, b: i8) -> i8
    ensures
        result as int == (if (a as int) < (b as int) { (a as int) } else { (b as int) }),
{
    if a < b { a } else { b }
}

/* helper modified by LLM (iteration 5): lemma relating sum of mins to spec-level min_total_fare */
fn lemma_min_sum(a: i8, b: i8, c: i8, d: i8)
    requires
        valid_input(a as int, b as int, c as int, d as int),
    ensures
        (min_i8(a, b) as int) + (min_i8(c, d) as int) == min_total_fare(a as int, b as int, c as int, d as int),
{
    proof {
        assert((min_i8(a, b) as int) == (if (a as int) < (b as int) { (a as int) } else { (b as int) }));
        assert((min_i8(c, d) as int) == (if (c as int) < (d as int) { (c as int) } else { (d as int) }));
        assert((min_i8(a, b) as int) + (min_i8(c, d) as int) == min_total_fare(a as int, b as int, c as int, d as int));
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int, d as int)
    ensures result as int == min_total_fare(a as int, b as int, c as int, d as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute minima and sum, and prove spec using lemma */
{
    let r1: i8 = min_i8(a, b);
    let r2: i8 = min_i8(c, d);
    let int_sum: int = (r1 as int) + (r2 as int);
    let result: i8 = int_sum as i8;
    proof {
        lemma_min_sum(a, b, c, d);
        assert((r1 as int) + (r2 as int) == min_total_fare(a as int, b as int, c as int, d as int));
        assert(result as int == min_total_fare(a as int, b as int, c as int, d as int));
    }
    result
}

// </vc-code>


}

fn main() {}
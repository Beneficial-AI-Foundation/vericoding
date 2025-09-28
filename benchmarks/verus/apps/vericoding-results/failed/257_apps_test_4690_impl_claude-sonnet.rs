// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000 && 1 <= d <= 10000
}

spec fn max_area(a: int, b: int, c: int, d: int) -> int {
    if a * b >= c * d { a * b } else { c * d }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to prove area bounds with explicit arithmetic proof */
proof fn lemma_area_bounds(a: int, b: int, c: int, d: int)
    requires
        valid_input(a, b, c, d)
    ensures
        a * b <= 100000000,
        c * d <= 100000000
{
    assert(a <= 10000 && b <= 10000);
    assert(c <= 10000 && d <= 10000);
    assert(a * b <= 10000 * 10000);
    assert(c * d <= 10000 * 10000);
    assert(10000 * 10000 == 100000000);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires 
        valid_input(a as int, b as int, c as int, d as int)
    ensures 
        result as int == max_area(a as int, b as int, c as int, d as int),
        result as int >= (a as int) * (b as int) && result as int >= (c as int) * (d as int),
        result as int == (a as int) * (b as int) || result as int == (c as int) * (d as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): cast to i32 to avoid overflow and back to i8 */
    proof {
        lemma_area_bounds(a as int, b as int, c as int, d as int);
    }
    
    let area1 = (a as i32) * (b as i32);
    let area2 = (c as i32) * (d as i32);
    
    if area1 >= area2 {
        proof {
            assert((area1 as int) == max_area(a as int, b as int, c as int, d as int));
        }
        area1 as i8
    } else {
        proof {
            assert((area2 as int) == max_area(a as int, b as int, c as int, d as int));
        }
        area2 as i8
    }
}
// </vc-code>


}

fn main() {}
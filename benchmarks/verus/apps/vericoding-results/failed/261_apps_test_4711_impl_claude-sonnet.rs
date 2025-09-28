// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000
}

spec fn min_of_three(x: int, y: int, z: int) -> int {
    if x <= y && x <= z { x }
    else if y <= z { y }
    else { z }
}

spec fn correct_result(a: int, b: int, c: int) -> int {
    min_of_three(a + b, a + c, b + c)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed return type to handle larger sums and fixed bounds lemma */
spec fn min_two(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

proof fn lemma_min_two_properties(x: int, y: int)
    ensures min_two(x, y) <= x,
        min_two(x, y) <= y,
        min_two(x, y) == x || min_two(x, y) == y
{
}

proof fn lemma_min_of_three_decomposition(x: int, y: int, z: int)
    ensures min_of_three(x, y, z) == min_two(min_two(x, y), z)
{
}

proof fn lemma_addition_bounds(a: i8, b: i8, c: i8)
    requires valid_input(a as int, b as int, c as int)
    ensures 2 <= (a as int) + (b as int) <= 20000,
        2 <= (a as int) + (c as int) <= 20000,
        2 <= (b as int) + (c as int) <= 20000
{
    assert(1 <= a as int <= 10000);
    assert(1 <= b as int <= 10000);
    assert(1 <= c as int <= 10000);
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8) -> (result: i8)
    requires valid_input(a as int, b as int, c as int)
    ensures result as int == correct_result(a as int, b as int, c as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use int arithmetic and cast result back to i8 */
    proof {
        lemma_addition_bounds(a, b, c);
    }
    
    let sum_ab = (a as int) + (b as int);
    let sum_ac = (a as int) + (c as int);
    let sum_bc = (b as int) + (c as int);
    
    let min_ab_ac = if sum_ab <= sum_ac { sum_ab } else { sum_ac };
    let result_int = if min_ab_ac <= sum_bc { min_ab_ac } else { sum_bc };
    
    proof {
        lemma_min_two_properties(sum_ab, sum_ac);
        lemma_min_two_properties(min_ab_ac, sum_bc);
        lemma_min_of_three_decomposition(sum_ab, sum_ac, sum_bc);
        assert(result_int >= 2 && result_int <= 20000);
        assert(result_int <= 127);
    }
    
    result_int as i8
}
// </vc-code>


}

fn main() {}
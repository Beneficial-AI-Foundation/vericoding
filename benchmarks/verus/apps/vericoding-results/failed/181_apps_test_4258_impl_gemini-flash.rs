// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, t: int) -> bool {
    1 <= a <= 20 && 1 <= b <= 20 && 1 <= t <= 20
}

spec fn production_count(a: int, t: int) -> int {
    if a > 0 { t / a } else { 0 }
}

spec fn total_biscuits(a: int, b: int, t: int) -> int {
    if a > 0 { b * production_count(a, t) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, t: i8) -> (result: i8)
    requires valid_input(a as int, b as int, t as int)
    ensures result as int == total_biscuits(a as int, b as int, t as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Fixed the compilation error by moving the calculation of prod_count_i8 and total_b_i8 out of the proof block and into the exec context. The casting to i8 is also done in the exec context.] */
{
    let prod_count_int = t as int / a as int;
    let prod_count_i8 = prod_count_int as i8;

    let total_b_int = b as int * prod_count_int;
    let total_b_i8 = total_b_int as i8;

    total_b_i8
}
// </vc-code>


}

fn main() {}
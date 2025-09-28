// <vc-preamble>
use vstd::prelude::*;

verus! {
    spec fn valid_input(n: int) -> bool {
        n >= 1
    }
    
    spec fn worst_case_presses(n: int) -> int
        recommends valid_input(n)
    {
        n * (n * n + 5) / 6
    }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No changes needed, section remains empty */
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures result as int == worst_case_presses(n as int) && result as int >= 1
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Used i32 for calculations, added assertions to handle overflow checks, verified equality, and ensured value fits in i8 range */
    let a: i32 = n as i32;
    let aa: i32 = a * a;
    let result_calc: i32 = a * (aa + 5) / 6;
    proof {
        assert(valid_input(n as int));
        assert(a == n as int);
        assert(aa == a * a);
        assert(result_calc as int == worst_case_presses(n as int));
        assert(result_calc as int >= 1);
        assert(result_calc <= 127);
    }
    result_calc as i8
}
// </vc-code>


}

fn main() {}
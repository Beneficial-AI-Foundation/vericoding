// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn triangular_number(n: int) -> int
    recommends n >= 0
{
    n * (n + 1) / 2
}

spec fn is_minimal_time(t: int, x: int) -> bool
    recommends x >= 1
{
    t >= 1 && 
    triangular_number(t) >= x &&
    (t == 1 || triangular_number(t - 1) < x)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by casting `t` to `int` within `triangular_number` function call, matching its `recommends` clause and ensuring proper type usage. */
    let x_int = x as int;

    let mut t: int = 1;

    while triangular_number(t) < x_int
        invariant
            x_int >= 1,
            t >= 1,
            triangular_number(t) >= triangular_number(1),
            (t > 1) ==> triangular_number(t - 1) < x_int,
        decreases x_int - triangular_number(t) 
    {
        t = t + 1;
    }
    
    t as i8
}
// </vc-code>


}

fn main() {}
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
/* helper modified by LLM (iteration 5): Limited i8 range for triangular calculation to prevent overflow */
fn triangular_number_exec(n: i8) -> (result: i8)
    requires
        n >= 1,
        n <= 15,
    ensures
        result as int == triangular_number(n as int),
{
    (n * (n + 1)) / 2
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Used i8 variables for exec calculations, fixed invariants and proof to avoid int usage */
{
    let mut t: i8 = 1;
    let mut tri: i8 = 0;
    while tri < x && t < 16
        invariant
            t >= 1,
            t <= 16,
            tri as int == triangular_number((t - 1) as int),
        decreases (16 - t)
    {
        tri = tri + t;
        t = t + 1;
    }
    proof {
        assert(triangular_number(t - 1) >= x as int);
        assert(t - 1 >= 1);
        if t - 1 > 1 {
            assert(triangular_number((t - 2) as int) < x as int);
        }
    }
    t - 1
}
// </vc-code>


}

fn main() {}
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
proof fn lemma_triangular_number_monotonic_increasing(n: int)
    requires n >= 0
    ensures triangular_number(n) <= triangular_number(n + 1)
{
    // Helper lemma showing triangular numbers are increasing
}

proof fn lemma_triangular_number_bounds(x: int, t: int)
    requires x >= 1, t >= 1
    ensures triangular_number(t - 1) < x ==> triangular_number(t) >= x || t == 1
{
    // Helper for boundary conditions
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified loop invariant and fixed decreases clause */
    let mut t: i8 = 1;
    let mut sum: i8 = 1;
    
    let ghost x_int = x as int;
    
    while sum < x
        invariant
            t >= 1,
            sum == triangular_number(t as int) as i8,
            triangular_number(t as int) <= x_int
        decreases x as int - sum as int
    {
        assert(sum + t + 1 == triangular_number((t + 1) as int) as i8);
        t = t + 1;
        sum = sum + t;
    }
    
    t
}
// </vc-code>


}

fn main() {}
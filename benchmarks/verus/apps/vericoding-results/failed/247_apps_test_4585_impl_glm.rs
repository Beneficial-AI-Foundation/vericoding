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
proof fn triangular_number_recurrence(n: int)
    recommends n >= 0
    ensures triangular_number(n+1) == triangular_number(n) + (n+1)
{
    assert(triangular_number(n+1) == (n+1)*(n+2)/2);
    assert(triangular_number(n) == n*(n+1)/2);
    assert((n+1)*(n+2) == n*(n+1) + 2*(n+1));
    assert((n+1)*(n+2)/2 == (n*(n+1) + 2*(n+1)) / 2);
    assert((n*(n+1) + 2*(n+1)) / 2 == n*(n+1)/2 + (n+1));
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): restructured loop to use non-ghost triangular computation */
    let mut t: i8 = 1;
    let x_int = x as int;
    let mut tri: int = 1; // triangular number for t=1
    while tri < x_int
        invariant
            1 <= t,
            tri == triangular_number(t as int),
            forall |k: int| 1 <= k < (t as int) ==> triangular_number(k) < x_int,
        decreases (x_int - tri) as nat
    {
        t = t + 1;
        tri = tri + (t as int);
    }
    t
}
// </vc-code>


}

fn main() {}
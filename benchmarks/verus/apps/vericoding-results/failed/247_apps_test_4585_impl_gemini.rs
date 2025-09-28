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
/* helper modified by LLM (iteration 4): added proof body for algebraic reasoning */
proof fn lemma_triangular_sum(n: int)
    requires n >= 0
    ensures triangular_number(n + 1) == triangular_number(n) + (n + 1)
{
    reveal(triangular_number);
    assert(2 * triangular_number(n + 1) == (n + 1) * (n + 2)) by(nonlinear_arith);
    assert(2 * (triangular_number(n) + (n + 1)) == n * (n + 1) + 2 * (n + 1)) by(nonlinear_arith);
    assert((n + 1) * (n + 2) == n * (n + 1) + 2 * (n + 1)) by(nonlinear_arith);
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added invariant to prove postcondition */
    let mut t: i8 = 0;
    let mut s: i32 = 0;
    while s < x as i32
        invariant
            t >= 0,
            s as int == triangular_number(t as int),
            t > 0 ==> triangular_number((t - 1) as int) < x as int,
        decreases (x as int) - (s as int)
    {
        proof {
            lemma_triangular_sum(t as int);
        }
        t = t + 1;
        s = s + t as i32;
    }
    t
}
// </vc-code>


}

fn main() {}
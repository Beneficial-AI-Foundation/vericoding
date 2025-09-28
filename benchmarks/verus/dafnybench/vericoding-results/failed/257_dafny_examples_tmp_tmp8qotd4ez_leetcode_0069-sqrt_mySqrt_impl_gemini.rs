// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sqrt(x: int, r: int) -> bool {
    r * r <= x && (r + 1) * (r + 1) > x
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for this simple linear search. */
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn mySqrt(x: int) -> (res: int)
    requires 0 <= x,
    ensures sqrt(x, res),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type errors by casting integer literals to 'int' and added a decreases clause. */
    let mut r: int = 0 as int;
    while (r + 1 as int) * (r + 1 as int) <= x
        invariant
            r >= 0,
            r * r <= x,
        decreases x - r * r
    {
        r = r + 1 as int;
    }
    r
}
// </vc-code>

}
fn main() {}
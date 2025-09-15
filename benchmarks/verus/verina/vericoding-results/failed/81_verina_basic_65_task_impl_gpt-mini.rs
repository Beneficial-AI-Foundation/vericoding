// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple square function for reasoning */
spec fn square(x: usize) -> usize { x * x }
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute integer sqrt using usize loop with invariants */
    let mut r: usize = 0;
    while (r + 1) * (r + 1) <= n
        invariant r <= n
        invariant r * r <= n
        decreases n - r
    {
        r = r + 1;
    }
    let res: usize = r;
    proof {
        assert(r * r <= n);
        assert(!((r + 1) * (r + 1) <= n));
        assert(n < (r + 1) * (r + 1));
    }
    res
}
// </vc-code>

}
fn main() {}
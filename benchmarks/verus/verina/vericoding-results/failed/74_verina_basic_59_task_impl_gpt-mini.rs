// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): proof that doubling twice equals quadruple */
proof fn lemma_double(x: i32)
    ensures
        2 * (2 * x) == 4 * x,
{
    proof {
        assert(2 * (2 * x) == (2 * 2) * x);
        assert((2 * 2) * x == 4 * x);
    }
}
// </vc-helpers>

// <vc-spec>
fn double_quadruple(x: i32) -> (result: (i32, i32))
    ensures
        result.0 == 2 * x,
        result.1 == 2 * result.0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute double and quadruple and invoke proof lemma */
    let a: i32 = 2 * x;
    let b: i32 = 2 * a;
    proof {
        lemma_double(x);
    }
    (a, b)
}
// </vc-code>

}
fn main() {}
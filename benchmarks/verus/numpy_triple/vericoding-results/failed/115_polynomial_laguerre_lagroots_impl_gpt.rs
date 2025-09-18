// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): keep int-based spec for linear root to reason about math without overflow */
spec fn linear_root(c0: int, c1: int) -> int { 1 + c0 / c1 }

/* helper modified by LLM (iteration 4): lemma stating the spec definition explicitly */
proof fn lemma_linear_root_def(c0: int, c1: int)
    ensures
        linear_root(c0, c1) == 1 + c0 / c1
{ }
// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i32>) -> (roots: Vec<i32>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] == 1 + c@[0] / c@[1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement degree-1 case; prove divisor non-zero before division */
    if c.len() == 2 {
        let a0 = c[0];
        let a1 = c[1];
        proof {
            assert(c.len() == 2);
            assert((c.len() - 1) as int == 1);
            assert(c@[c.len() - 1 as int] != 0);
            assert(c@[1] != 0);
            assert(a1 == c@[1]);
            assert(a1 != 0);
        }
        let q = a0 / a1; // division safe because a1 != 0
        let root = q + 1i32; // compute final root
        let mut v: Vec<i32> = Vec::new();
        v.push(root);
        v
    } else {
        Vec::new()
    }
}
// </vc-code>

}
fn main() {}
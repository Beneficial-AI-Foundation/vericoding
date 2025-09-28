// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed placeholder helper, not needed. */
fn no_helpers_needed() { }
// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i8>) -> (roots: Vec<i8>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] as int == 1 + c@[0] as int / c@[1] as int,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected indexing into Seq<i8> by dereferencing c to a sequence using `@`. */
{
    if c.len() == 2 {
        let root_val: i8 = -(c@.index(0)) / (c@.index(1));
        let mut roots: Vec<i8> = Vec::new();
        roots.push(root_val);
        roots
    } else {
        // This case is not covered by the current ensures clauses
        // A more general solution for polynomial roots would be needed
        Vec::new()
    }
}
// </vc-code>

}
fn main() {}
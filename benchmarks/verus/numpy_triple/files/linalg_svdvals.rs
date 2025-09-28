// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn min_nat(a: nat, b: nat) -> nat {
    if a <= b { a } else { b }
}

fn svdvals(x: Vec<Vec<i8>>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
        x@.len() < usize::MAX,
        x@[0].len() > 0,
    ensures 
        result@.len() == min_nat(x@.len() as nat, x@[0].len() as nat),
        /* Property 1: All singular values are non-negative */
        forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] >= 0,
        /* Property 2: Singular values are sorted in descending order */
        forall|i: int, j: int| 0 <= i <= j < result@.len() ==> #[trigger] result@[i] >= #[trigger] result@[j],
        /* Property 4: If the matrix is zero, all singular values are zero */
        (forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@[i].len() ==> #[trigger] x@[i][j] == 0) ==>
            (forall|i: int| 0 <= i < result@.len() ==> #[trigger] result@[i] == 0)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}
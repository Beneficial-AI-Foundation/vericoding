// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermegauss(deg: usize) -> (result: (Vec<i8>, Vec<i8>))
    requires deg > 0,
    ensures
        /* Points are ordered (sorted in ascending order) */
        forall|i: int, j: int| 0 <= i < j < deg ==> (result.0@[i] as int) < (result.0@[j] as int),
        /* Weights are positive */
        forall|i: int| 0 <= i < deg ==> (result.1@[i] as int) > 0,
        /* Return tuple has correct lengths */
        result.0@.len() == deg && result.1@.len() == deg,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    (Vec::new(), Vec::new())
    // impl-end
}
// </vc-code>


}
fn main() {}
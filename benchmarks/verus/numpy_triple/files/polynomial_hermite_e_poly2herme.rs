// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn poly2herme(pol: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == pol.len(),
        forall|i: int| 0 <= i < pol@.len() && pol@[i] != 0 ==> exists|j: int| 0 <= j < result@.len() && result@[j] != 0,
        (exists|i: int| 0 <= i < pol@.len() && pol@[i] != 0) ==> (exists|j: int| 0 <= j < result@.len() && result@[j] != 0),
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
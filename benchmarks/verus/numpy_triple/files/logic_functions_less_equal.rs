// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn less_equal(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1@.len() ==> result@[i] == (x1@[i] <= x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (result@[i] == true <==> x1@[i] <= x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (result@[i] == false <==> x1@[i] > x2@[i]),
        forall|i: int| 0 <= i < x1@.len() ==> (x1@[i] == x2@[i] ==> result@[i] == true),
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
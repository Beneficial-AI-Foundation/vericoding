// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sign(x: Vec<i8>) -> (result: Vec<i8>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> {
            (x@[i] < 0 ==> result@[i] == -1) &&
            (x@[i] == 0 ==> result@[i] == 0) &&
            (x@[i] > 0 ==> result@[i] == 1)
        }
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
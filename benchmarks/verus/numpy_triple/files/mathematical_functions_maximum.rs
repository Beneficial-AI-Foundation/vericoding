// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maximum(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] == if x1@[i] >= x2@[i] { x1@[i] } else { x2@[i] },
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] >= x1@[i] && result@[i] >= x2@[i],
        forall|i: int| 0 <= i < result.len() ==> 
            result@[i] == x1@[i] || result@[i] == x2@[i],
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
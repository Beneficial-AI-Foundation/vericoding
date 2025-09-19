// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn extract(condition: Vec<bool>, arr: Vec<i8>) -> (result: Vec<i8>)
    requires condition.len() == arr.len(),
    ensures

        forall|k: int| 0 <= k < result@.len() ==> 
            exists|i: int| 0 <= i < condition@.len() && condition@[i] && #[trigger] result@[k] == arr@[i],

        forall|k1: int, k2: int| 0 <= k1 < k2 < result@.len() ==>
            exists|i1: int, i2: int| 
                0 <= i1 < i2 < condition@.len() && 
                condition@[i1] && condition@[i2] &&
                #[trigger] result@[k1] == arr@[i1] && #[trigger] result@[k2] == arr@[i2],

        forall|i: int| 0 <= i < condition@.len() && condition@[i] ==>
            exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == #[trigger] arr@[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
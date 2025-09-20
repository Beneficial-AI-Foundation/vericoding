// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn numpy_cos(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -1 <= result@[i] as int <= 1 &&
            (x@[i] as int == 0 ==> result@[i] as int == 1)
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
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_arctanh(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
    ensures
        result@.len() == x@.len(),
        /* Identity property: arctanh(0) = 0 */
        forall|i: int| 0 <= i < x@.len() && x@[i] as int == 0 ==> result@[i] as int == 0,
        /* Range property: result contains finite numbers */
        result@.len() == x@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix verification error */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i && x@[j] as int == 0 ==> result@[j] as int == 0,
        decreases x.len() - i
    {
        if x[i] == 0 {
            result.push(0);
        } else {
            result.push(x[i]);
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}
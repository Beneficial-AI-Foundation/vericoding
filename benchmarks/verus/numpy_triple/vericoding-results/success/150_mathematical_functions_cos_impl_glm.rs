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
    let mut result = Vec::with_capacity(x.len());
    for i in 0..x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < result@.len() ==> {
                -1 <= result@[j] as int <= 1 &&
                (x@[j] as int == 0 ==> result@[j] as int == 1)
            }
    {
        let val = x[i];
        let cos_val = if val == 0 { 1 } else { 0 };
        result.push(cos_val);
    }
    result
}
// </vc-code>


}
fn main() {}
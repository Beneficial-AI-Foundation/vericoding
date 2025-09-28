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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> {
                -1 <= result@[j] as int <= 1 &&
                (x@[j] as int == 0 ==> result@[j] as int == 1)
            }
        decreases x.len() - i
    {
        let cos_val = if x[i] == 0 { 1i8 } else { 0i8 };
        result.push(cos_val);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}
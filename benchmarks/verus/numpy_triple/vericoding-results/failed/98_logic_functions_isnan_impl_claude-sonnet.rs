// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x@.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed problematic proof block assertion */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] == true <==> x@[j] != x@[j]),
            0 <= i <= x.len(),
        decreases x.len() - i
    {
        let is_nan = x[i] != x[i];
        result.push(is_nan);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
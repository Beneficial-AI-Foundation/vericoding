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
/* code modified by LLM (iteration 5): use is_nan() to correctly bridge exec and spec for NaN checks */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> (result@[j] <==> (x@[j] != x@[j])),
        decreases x.len() - i
    {
        let is_nan_val = x[i].is_nan();
        result.push(is_nan_val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
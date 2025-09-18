// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed f64 type handling */
fn is_f64_nan(x: f64) -> bool { x != x }
// </vc-helpers>

// <vc-spec>
fn isnan(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added loop invariant to track length and element correctness */
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] == true <==> x@[j] != x@[j])
    {
        let val = is_f64_nan(x[i]);
        result.push(val);
    }
    result
}
// </vc-code>

}
fn main() {}
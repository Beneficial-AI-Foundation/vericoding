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
/* code modified by LLM (iteration 5): Remove hist and push_ensures, correctly use result[@j] for invariant conditions. */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i as int,
            i as int <= x.len() as int,
            result.len() == i,
            // For elements already processed, the condition holds
            forall|j: int| 0 <= j < i ==> (result@.index(j) == true <==> x[j] != x[j]),
            forall|j: int| 0 <= j < i ==> (result@.index(j) == true ==> x[j] != x[j]),
            forall|j: int| 0 <= j < i ==> (x[j] == x[j] ==> result@.index(j) == false),
        decreases x.len() - i
    {
        if x[i] != x[i] {
            result.push(true);
        } else {
            result.push(false);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
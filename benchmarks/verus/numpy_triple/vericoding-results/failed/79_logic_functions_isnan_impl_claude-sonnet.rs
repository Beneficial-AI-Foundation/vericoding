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
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true <==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (result[i] == true ==> x[i] != x[i]),
        forall|i: int| 0 <= i < x.len() ==> (x[i] == x[i] ==> result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified proof by removing explicit assertions that failed */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result[j] == true <==> x[j] != x[j]),
            forall|j: int| 0 <= j < i ==> (result[j] == true ==> x[j] != x[j]),
            forall|j: int| 0 <= j < i ==> (x[j] == x[j] ==> result[j] == false)
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
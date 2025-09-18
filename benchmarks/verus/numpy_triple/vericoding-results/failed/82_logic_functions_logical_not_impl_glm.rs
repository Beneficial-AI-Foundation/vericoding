// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed while loop syntax by adding body block */
    let n = x.len() as int;
    let mut result = Vec::new();
    let mut i = 0;
    while i < n
        invariant { 0 <= i <= n }
        invariant { result.len() == i }
        invariant { forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] == 0.0) }
    {
        result.push(x@[i] == 0.0);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
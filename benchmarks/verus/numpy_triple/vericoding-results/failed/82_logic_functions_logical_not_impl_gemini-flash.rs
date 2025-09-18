// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed unnecessary helper as the compilation error was due to `nat` and `int` usage in `Vec::with_capacity` in ghost code. */
// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `x.len() as nat` to `x.len()` in `Vec::with_capacity` to resolve the compilation error. */
{
    let mut result: Vec<bool> = Vec::with_capacity(x.len());
    let mut i = 0;

    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            result.len() <= result.capacity(),
            forall|j: int| 0 <= j < i ==> result[j] == (x[j] == 0.0)
        decreases x.len() - i
    {
        result.push(x[i] == 0.0);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
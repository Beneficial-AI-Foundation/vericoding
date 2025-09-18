// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): use floating point comparison in exec context */
fn f32_min(a: f32, b: f32) -> f32 {
    if a <= b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn fmin(x: Vec<f32>, y: Vec<f32>) -> (result: Vec<f32>)
    requires x.len() == y.len(),
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> #[trigger] result[i] == x[i] || #[trigger] result[i] == y[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): add bounds checks to invariant and fix indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            x.len() == y.len(),
            i <= x.len(),
            i <= y.len(),
            forall|j: int| 0 <= j < i ==> result[j] == x[j] || result[j] == y[j]
        decreases x.len() - i
    {
        let min_val = if i < x.len() && i < y.len() && x[i] <= y[i] { x[i] } else { y[i] };
        result.push(min_val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
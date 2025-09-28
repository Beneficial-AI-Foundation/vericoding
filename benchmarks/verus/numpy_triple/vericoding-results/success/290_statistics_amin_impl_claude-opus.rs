// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn in_array(result: f32, a: Seq<f32>) -> bool {
    exists|i: int| 0 <= i < a.len() && result == a[i]
}

fn amin(a: Vec<f32>) -> (result: f32)
    requires a.len() > 0,
    ensures in_array(result, a@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to fix loop verification */
    let mut min_val = a[0];
    let mut i = 1;
    while i < a.len()
        invariant
            0 < i <= a.len(),
            in_array(min_val, a@),
        decreases a.len() - i
    {
        if a[i] < min_val {
            min_val = a[i];
        }
        i = i + 1;
    }
    min_val
}
// </vc-code>

}
fn main() {}
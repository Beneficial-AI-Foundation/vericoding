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
    /* code modified by LLM (iteration 4): removed invariant with unsupported f32 comparison */
    let mut min_val = a[0];
    let mut i: usize = 1;
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            exists|k: int| 0 <= k < (i as int) && min_val == a@[k],
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
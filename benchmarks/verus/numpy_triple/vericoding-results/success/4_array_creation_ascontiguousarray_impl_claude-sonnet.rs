// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ascontiguousarray(a: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        a.len() > 0 ==> result.len() == a.len(),
        a.len() == 0 ==> result.len() == 1,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == a[i],
        a.len() == 0 ==> result.len() == 1 && result[0] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        let mut result = Vec::new();
        result.push(0.0f32);
        result
    } else {
        let mut result = Vec::new();
        for i in 0..a.len()
            invariant
                result.len() == i,
                forall|j: int| 0 <= j < i ==> #[trigger] result[j] == a[j],
        {
            result.push(a[i]);
        }
        result
    }
}
// </vc-code>

}
fn main() {}
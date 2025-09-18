// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn is_non_empty(a: Vec<f32>) -> bool { a.len() > 0 }
fn get_zero_vec() -> Vec<f32> { vec![0.0f32] }
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
    if a.len() > 0 {
        a
    } else {
        vec![0.0f32]
    }
}
// </vc-code>

}
fn main() {}
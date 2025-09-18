// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn singleton_f32(x: f32) -> (result: Vec<f32>)
    ensures
        result.len() == 1,
        result[0] == x
{
    let mut v: Vec<f32> = Vec::new();
    v.push(x);
    v
}
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
        singleton_f32(0.0f32)
    }
}
// </vc-code>

}
fn main() {}
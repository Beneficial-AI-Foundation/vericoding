// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_full_like(a: Vec<f32>, fill_value: f32) -> (result: Vec<f32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<f32> = Vec::new();
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == fill_value,
        decreases n - i
    {
        result.push(fill_value);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn atleast_3d(arr: Vec<f32>) -> (result: Vec<Vec<Vec<f32>>>)
    ensures 
        result.len() == 1,
        forall|j: int| 0 <= j < 1 ==> #[trigger] result[j].len() == arr.len(),
        forall|j: int, k: int| 0 <= j < 1 && 0 <= k < arr.len() ==> #[trigger] result[j][k].len() == 1,
        forall|i: int| 0 <= i < arr.len() ==> {
            let outer = &result[0];
            let middle = &outer[i];
            let value = middle[0];
            value == #[trigger] arr[i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut outer: Vec<Vec<Vec<f32>>> = Vec::new();
    let mut middle: Vec<Vec<f32>> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            middle.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] middle[j].len() == 1,
            forall|j: int| 0 <= j < i ==> #[trigger] middle[j][0] == arr[j]
        decreases arr.len() - i
    {
        let mut inner: Vec<f32> = Vec::new();
        inner.push(arr[i]);
        middle.push(inner);
        i = i + 1;
    }
    outer.push(middle);
    outer
}
// </vc-code>

}
fn main() {}
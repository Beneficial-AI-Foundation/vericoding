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
    /* code modified by LLM (iteration 2): added decreases clause to the while loop */
    let mut middle: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            middle.view().len() == i as int,
            forall|k: int| 0 <= k < i as int ==> #[trigger] middle.view()[k].len() == 1,
            forall|k: int| 0 <= k < i as int ==> #[trigger] middle.view()[k][0] == arr.view()[k],
        decreases arr.len() - i
    {
        let inner = vec![arr[i]];
        middle.push(inner);
        i = i + 1;
    }
    let result = vec![middle];
    result
}
// </vc-code>

}
fn main() {}
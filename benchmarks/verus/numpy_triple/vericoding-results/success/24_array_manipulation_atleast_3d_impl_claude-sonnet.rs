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
    let mut result: Vec<Vec<Vec<f32>>> = Vec::new();
    let mut outer_vec: Vec<Vec<f32>> = Vec::new();
    
    for i in 0..arr.len()
        invariant
            outer_vec.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] outer_vec[k].len() == 1,
            forall|k: int| 0 <= k < i ==> outer_vec[k][0] == #[trigger] arr[k]
    {
        let mut inner_vec: Vec<f32> = Vec::new();
        inner_vec.push(arr[i]);
        outer_vec.push(inner_vec);
    }
    
    result.push(outer_vec);
    result
}
// </vc-code>

}
fn main() {}
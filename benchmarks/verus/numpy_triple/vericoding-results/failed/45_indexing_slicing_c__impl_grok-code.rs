// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<f32>, arr2: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i].len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
[
/* code modified by LLM (iteration 5): corrected invariant syntax by removing invalid #![auto] attribute */
    let mut result: Vec<Vec<f32>> = Vec::new();
    for i in 0..arr1.len()
    invariant
        result.len() == i,
        forall|j: int| 0 <= j < i ==> 
            result[j].len() == 2 &&
            result[j][0] == arr1[j] &&
            result[j][1] == arr2[j]
    {
        proof {
            assert(arr1.len() == arr2.len());
            assert(i < arr1.len());
            assert(i < arr2.len());
        }
        let mut inner = Vec::new();
        inner.push(arr1[i]);
        inner.push(arr2[i]);
        result.push(inner);
    }
    result
}
// </vc-code>

}
fn main() {}
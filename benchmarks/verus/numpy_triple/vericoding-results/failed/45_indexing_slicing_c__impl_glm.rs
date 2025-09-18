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
{
    let mut result = Vec::new();
    let n = arr1.len();
    for i in 0..n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j as usize].len() == 2 &&
                result[j as usize][0] == arr1[j as usize] &&
                result[j as usize][1] == arr2[j as usize]
    {
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
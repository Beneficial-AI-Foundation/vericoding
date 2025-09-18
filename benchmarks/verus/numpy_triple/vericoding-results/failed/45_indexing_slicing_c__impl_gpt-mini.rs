// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): create pair vector */
fn make_pair(a: f32, b: f32) -> Vec<f32> { let mut v = Vec::<f32>::new(); v.push(a); v.push(b); v }
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
    /* code modified by LLM (iteration 5): build result vector of pairs with invariants and proof */
    let mut result = Vec::<Vec<f32>>::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant i <= arr1.len()
        invariant result.len() == i
        invariant forall |j: usize| j < i ==> result[j].len() == 2 && result[j][0] == arr1[j] && result[j][1] == arr2[j]
        decreases arr1.len() - i
    {
        let mut pair = Vec::<f32>::new();
        pair.push(arr1[i]);
        pair.push(arr2[i]);
        result.push(pair);
        i = i + 1;
    }
    proof {
        assert(result.len() == arr1.len());
        assert(forall |k: int| 0 <= k && k < result.len() as int ==> result[k as usize].len() == 2 && result[k as usize][0] == arr1[k as usize] && result[k as usize][1] == arr2[k as usize]);
    }
    result
}
// </vc-code>

}
fn main() {}
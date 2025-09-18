// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding a placeholder helper. */
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
/* code modified by LLM (iteration 5): Ensured usize casting for indexing while keeping int for comparison and quantifiers. */
{
    let mut result = Vec::new();
    let len = arr1.len();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i as int,
            (i as int) <= (len as int),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> ([result@j]).len() == (2 as nat) && ([result@j])[0] == ([arr1@j as usize]) && ([result@j])[1] == ([arr2@j as usize])
    {
        let mut pair = Vec::new();
        pair.push(arr1[i]);
        pair.push(arr2[i]);
        result.push(pair);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<i8>, arr2: Vec<i8>) -> (result: Vec<Vec<i8>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i]@.len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant to use result.len() in quantifier condition */
{
    let mut result: Vec<Vec<i8>> = Vec::new();
    let n = arr1.len();
    for i in 0..n
        invariant
            arr1@.len() == n,
            arr2@.len() == n,
            result.len() == i,
            i <= n,
            forall|j: int| 0 <= j < result.len() ==> 
                result[j]@.len() == 2 && 
                result[j][0] == arr1[j] && 
                result[j][1] == arr2[j]
        decreases n - i
    {
        let inner = vec![arr1[i], arr2[i]];
        result.push(inner);
    }
    result
}
// </vc-code>

}
fn main() {}
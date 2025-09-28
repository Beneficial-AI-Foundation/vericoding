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
{
/* code modified by LLM (iteration 5): fixed compilation error by using usize for loop variable instead of int */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            result@.len() == i as int,
            arr1@.len() == arr2@.len(),
            forall|j: int| #![trigger result@[j]] 0 <= j < i as int ==>
                result@[j]@.len() == 2 &&
                result@[j][0] == arr1@[j] &&
                result@[j][1] == arr2@[j],
        decreases (arr1@.len() - i as int)
    {
        let mut inner: Vec<i8> = Vec::new();
        inner.push(arr1[i]);
        inner.push(arr2[i]);
        result.push(inner);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
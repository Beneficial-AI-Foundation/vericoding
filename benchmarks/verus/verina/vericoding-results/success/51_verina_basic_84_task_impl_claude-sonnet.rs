// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace(arr: &Vec<i32>, k: i32) -> (result: Vec<i32>)
    ensures
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] > k ==> result[i] == -1),
        forall|i: int| 0 <= i < arr.len() ==> (arr[i] <= k ==> result[i] == arr[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): initialize Vec with correct capacity for length postcondition */
    let mut result = Vec::with_capacity(arr.len());
    let mut i = 0;
    while i < arr.len()
        invariant
            result.len() == i,
            i <= arr.len(),
            forall|j: int| 0 <= j < i ==> (arr[j] > k ==> result[j] == -1),
            forall|j: int| 0 <= j < i ==> (arr[j] <= k ==> result[j] == arr[j]),
        decreases arr.len() - i
    {
        if arr[i] > k {
            result.push(-1);
        } else {
            result.push(arr[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
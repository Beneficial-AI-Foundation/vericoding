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
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
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
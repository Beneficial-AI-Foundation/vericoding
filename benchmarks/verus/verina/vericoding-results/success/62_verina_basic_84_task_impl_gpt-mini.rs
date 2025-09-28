// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec function to choose replacement value */
spec fn choose_replacement(x: i32, k: i32) -> i32 {
    if x > k { -1i32 } else { x }
}

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
    /* code modified by LLM (iteration 3): iterate array and replace >k with -1 */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> (arr[j] > k ==> result[j] == -1i32),
            forall|j: int| 0 <= j && j < i as int ==> (arr[j] <= k ==> result[j] == arr[j]),
        decreases arr.len() - i
    {
        if arr[i] > k {
            result.push(-1i32);
        } else {
            result.push(arr[i]);
        }
        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}
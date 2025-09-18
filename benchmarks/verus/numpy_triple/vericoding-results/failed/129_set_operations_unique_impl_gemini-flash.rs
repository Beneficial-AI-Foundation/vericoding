// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): contains function for Vec<i32> */
spec fn contains(vec: &Vec<i32>, val: i32) -> bool {
    exists|i: int| #![auto]
        0 <= i < vec.len() && vec[i] == val
}
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> result[i] < result[j],

        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[i] == arr[j],

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int| #![trigger arr[i]] 0 <= i < arr.len() ==> exists|j: int| 0 <= j < result.len() && arr[i] == result[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): reformatted the invariant as reported by the compiler error */
{
    let mut result = Vec::<i32>::new();
    let mut i = 0;

    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] < result[y],
            forall|k: int| 0 <= k < result.len() ==> contains(&arr, result[k]),
            forall|k: int| 0 <= k < i ==> {
                contains(&result, arr[k]) || (!contains(&result, arr[k]) && forall|m: int| 0 <= m < k && m != k ==> arr[m] != arr[k])
            },
        decreases arr.len() - i
    {
        if !contains(&result, arr[i]) {
            let mut j = 0;
            while j < result.len() && arr[i] > result[j]
                invariant 
                    forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] < result[y],
                    0 <= j <= result.len(),
                    forall|k: int| 0 <= k < result.len() ==> contains(&arr, result[k]),
                    forall|k: int| 0 <= k < j ==> result[k] < arr[i],
                decreases result.len() - j
            {
                j = j + 1;
            }
            result.insert(j as int, arr[i]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
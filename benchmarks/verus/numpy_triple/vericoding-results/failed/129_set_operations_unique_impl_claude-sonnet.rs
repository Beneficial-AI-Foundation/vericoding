// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added triggers to fix verification error */
fn contains(arr: &Vec<i32>, val: i32) -> (res: bool)
    ensures res == exists|k: int| #![trigger arr[k]] 0 <= k < arr.len() && arr[k] == val
{
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            forall|k: int| #![trigger arr[k]] 0 <= k < i ==> arr[k] != val
        decreases arr.len() - i
    {
        if arr[i] == val {
            return true;
        }
        i += 1;
    }
    false
}

spec fn is_sorted_unique(arr: Vec<i32>) -> bool {
    forall|i: int, j: int| #![trigger arr[i], arr[j]] 0 <= i < j < arr.len() ==> arr[i] < arr[j]
}

spec fn contains_subseq(arr: Vec<i32>, start: int, end: int, val: i32) -> bool {
    exists|k: int| #![trigger arr[k]] start <= k < end && k < arr.len() && arr[k] == val
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
{
    /* code modified by LLM (iteration 5): added triggers to fix verification error */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            is_sorted_unique(result),
            forall|k: int| #![trigger result[k]] 0 <= k < result.len() ==> contains_subseq(arr, 0, i as int, result[k]),
            forall|k: int| #![trigger arr[k]] 0 <= k < i ==> exists|j: int| 0 <= j < result.len() && arr[k] == result[j]
        decreases arr.len() - i
    {
        let val = arr[i];
        if !contains(&result, val) {
            let mut pos: usize = 0;
            while pos < result.len() && result[pos] < val
                invariant
                    pos <= result.len(),
                    forall|k: int| #![trigger result[k]] 0 <= k < pos ==> result[k] < val,
                    forall|k: int| #![trigger result[k]] pos <= k < result.len() ==> result[k] >= val
                decreases result.len() - pos
            {
                pos += 1;
            }
            
            if pos < result.len() && result[pos] == val {
                // Already exists, skip
            } else {
                result.insert(pos, val);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
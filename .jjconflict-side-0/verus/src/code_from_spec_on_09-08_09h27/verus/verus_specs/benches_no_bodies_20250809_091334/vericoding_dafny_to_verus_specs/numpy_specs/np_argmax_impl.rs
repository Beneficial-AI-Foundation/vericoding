use vstd::prelude::*;

verus! {

// SPEC
fn argmax(arr: &[int]) -> (ret: usize)
    requires 
        arr.len() > 0,
    ensures
        ret < arr.len(),
        forall|i: int| 0 <= i < ret ==> arr[ret as int] > arr[i],
        forall|i: int| ret < i < arr.len() ==> arr[ret as int] >= arr[i],
{
    let mut max_idx = 0;
    let mut i = 1;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < arr.len()
        invariant
            0 <= max_idx < arr.len(),
            1 <= i <= arr.len(),
            forall|j: int| 0 <= j < max_idx ==> arr[max_idx as int] > arr[j],
            forall|j: int| max_idx < j < i ==> arr[max_idx as int] >= arr[j],
        decreases arr.len() - i
    {
        if arr[i] >= arr[max_idx] {
            max_idx = i;
        }
        i += 1;
    }
    
    max_idx
}

fn main() {}

}
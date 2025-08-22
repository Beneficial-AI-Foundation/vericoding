use vstd::prelude::*;

verus! {

spec fn check_find_first_odd(arr: &Vec<u32>, index: Option<usize>) -> (result: bool)
{
    if let Some(idx) = index {
        &&& idx < arr.len()
        &&& arr[idx as int] % 2 != 0
        &&& forall|k: int| 0 <= k < idx ==> arr[k] % 2 == 0
    } else {
        forall|k: int| 0 <= k < arr.len() ==> (arr[k] % 2 == 0)
    }
}

fn find_first_odd(arr: &Vec<u32>) -> (index: Option<usize>)
    ensures check_find_first_odd(arr, index),
{
    let mut i = 0;
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] % 2 == 0,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            return Some(i);
        }
        i += 1;
    }
    None
}

} // verus!

fn main() {}
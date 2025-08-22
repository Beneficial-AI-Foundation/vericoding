use vstd::prelude::*;

fn main() {
    // Example usage
    let v = vec![1, 2, 3, 4, 5];
    if v.len() > 0 {
        let sorted = is_sorted(&v);
        println!("Vector is sorted: {}", sorted);
    }
}

verus! {

fn is_sorted(arr: &Vec<i32>) -> (is_sorted: bool)
    requires
        arr.len() > 0,
    ensures
        is_sorted == (forall|i: int, j: int| 0 <= i < j < arr.len() ==> (arr[i] <= arr[j])),
{
    let mut idx = 0;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while idx < arr.len() - 1
        invariant
            0 <= idx < arr.len(),
            forall|i: int, j: int| 0 <= i < j < idx + 1 ==> (arr[i] <= arr[j]),
        decreases arr.len() - 1 - idx,
    {
        if arr[idx] > arr[idx + 1] {
            return false;
        }
        idx += 1;
    }
    true
}

} // verus!
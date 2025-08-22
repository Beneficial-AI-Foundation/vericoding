#![crate_name="barrier"]

use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
{
    if arr.len() == 0 || p >= arr.len() - 1 {
        return true;
    }
    
    let mut max_left = arr[0];
    let mut i = 1;
    while i <= p
        invariant
            0 < i <= p + 1,
            p < arr.len(),
            max_left == arr@.subrange(0, i as int).fold_left(arr[0], |acc: i32, x: i32| if acc >= x { acc } else { x }),
            forall|j: int| 0 <= j < i ==> arr[j] <= max_left,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases p + 1 - i
    {
        if arr[i] > max_left {
            max_left = arr[i];
        }
        i += 1;
    }
    
    let mut min_right = arr[p + 1];
    let mut j = p + 2;
    while j < arr.len()
        invariant
            p + 1 < j <= arr.len(),
            p < arr.len(),
            min_right == arr@.subrange(p as int + 1, j as int).fold_left(arr[p + 1], |acc: i32, x: i32| if acc <= x { acc } else { x }),
            forall|k: int| p < k < j ==> arr[k] >= min_right,
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases arr.len() - j
    {
        if arr[j] < min_right {
            min_right = arr[j];
        }
        j += 1;
    }
    
    max_left < min_right
}

fn main() {}
}
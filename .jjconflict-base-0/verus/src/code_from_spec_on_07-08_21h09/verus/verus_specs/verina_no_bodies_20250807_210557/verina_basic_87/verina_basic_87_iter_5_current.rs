use vstd::prelude::*;

verus! {

fn update_array_element(arr: &mut Vec<i32>, i: usize, j: usize)
    requires 
        i < arr@.len(),
        j < arr@.len(),
    ensures
        arr@.len() == old(arr)@.len(),
        arr@[i as int] == old(arr)@[j as int],
{
    /* code modified by LLM (iteration 3): Fixed array assignment to use proper mutable reference assignment */
    arr.set(i, arr[j]);
}

fn main() {}

}
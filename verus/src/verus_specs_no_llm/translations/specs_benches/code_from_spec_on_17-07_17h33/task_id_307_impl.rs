use vstd::prelude::*;

verus! {

//IMPL list_deep_clone
fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    /* code modified by LLM (iteration 2): Added decreases clause to prove loop termination */
    let mut copied = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            copied@.len() == i,
            forall|j: int| (0 <= j < i) ==> arr[j] == copied[j],
        decreases arr.len() - i,
    {
        copied.push(arr[i]);
        i += 1;
    }
    
    copied
}

} // verus!

fn main() {}
use vstd::prelude::*;

verus! {

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    // post-conditions-start
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
    // post-conditions-end
{
    let mut copied = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause and strengthened invariant to help prove postcondition */
    while i < arr.len()
        invariant
            copied@.len() == i,
            forall|j: int| (0 <= j < i) ==> arr[j] == copied[j],
            i <= arr@.len(),
        decreases arr@.len() - i
    {
        copied.push(arr[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to help Verus connect loop exit condition with postcondition */
    assert(i == arr@.len());
    assert(copied@.len() == i);
    
    copied
}

} // verus!

fn main() {}
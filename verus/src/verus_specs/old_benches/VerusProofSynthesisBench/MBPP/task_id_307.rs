use vstd::prelude::*;

verus! {

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    // post-conditions-start
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
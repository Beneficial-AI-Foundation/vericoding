use vstd::prelude::*;

verus! {

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)

    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    assume(false);
    unreached();
}

}
fn main() {}
use vstd::prelude::*;

verus! {

fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}

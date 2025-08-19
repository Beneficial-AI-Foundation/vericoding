use vstd::prelude::*;

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
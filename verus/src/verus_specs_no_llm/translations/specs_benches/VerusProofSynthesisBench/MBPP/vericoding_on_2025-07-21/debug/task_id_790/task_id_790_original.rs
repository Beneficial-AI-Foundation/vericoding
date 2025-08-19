use vstd::prelude::*;


verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
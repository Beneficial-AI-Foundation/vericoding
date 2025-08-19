use vstd::prelude::*;

verus! {

fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)
    // post-conditions-start
    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}

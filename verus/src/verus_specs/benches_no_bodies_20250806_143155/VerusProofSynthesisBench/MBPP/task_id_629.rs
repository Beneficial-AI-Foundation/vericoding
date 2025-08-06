use vstd::prelude::*;


verus! {

fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)
    // post-conditions-start
    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
    // post-conditions-end
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}

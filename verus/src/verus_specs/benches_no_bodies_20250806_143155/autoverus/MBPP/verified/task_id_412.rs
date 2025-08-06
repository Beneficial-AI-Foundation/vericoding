use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)
    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

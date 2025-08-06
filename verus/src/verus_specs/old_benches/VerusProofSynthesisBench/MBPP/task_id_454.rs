use vstd::prelude::*;

verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}

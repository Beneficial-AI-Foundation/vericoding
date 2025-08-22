use vstd::prelude::*;

verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
    // post-conditions-end
{
    for i in 0..text.len()
        invariant
            !(exists|j: int| 0 <= j < i && (text[j] == 'Z' || text[j] == 'z')),
    {
        if text[i] == 'Z' || text[i] == 'z' {
            return true;
        }
    }
    false
}

} // verus!

fn main() {}
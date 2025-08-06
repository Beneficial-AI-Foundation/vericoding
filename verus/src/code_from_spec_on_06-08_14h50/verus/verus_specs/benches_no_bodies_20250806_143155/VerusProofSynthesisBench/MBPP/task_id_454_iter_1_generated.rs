use vstd::prelude::*;

verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
    // post-conditions-end
{
    for j in 0..text.len()
        invariant
            forall|i: int| 0 <= i < j ==> text[i] != 'Z' && text[i] != 'z',
    {
        if text[j] == 'Z' || text[j] == 'z' {
            return true;
        }
    }
    false
}

} // verus!

fn main() {}
use vstd::prelude::*;

verus! {

fn contains_z(text: &Vec<char>) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
{
    let mut index = 0;
    while index < text.len()
        invariant
            0 <= index <= text.len(),
            forall|k: int| 0 <= k < index ==> (text[k] != 'Z' && text[k] != 'z'),
    {
        if text[index] == 'Z' || text[index] == 'z' {
            return true;
        }
        index += 1;
    }
    false
}

fn main() {}

} // verus!

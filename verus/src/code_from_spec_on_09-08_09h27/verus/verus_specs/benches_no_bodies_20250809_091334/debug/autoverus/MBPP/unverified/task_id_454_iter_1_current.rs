use vstd::prelude::*;

fn main() {}

verus! {

fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    for i in 0..text.len()
        invariant
            !(exists|j: int| 0 <= j < i && (text[j] == 90 || text[j] == 122)),
    {
        if text[i] == 90 || text[i] == 122 {
            return true;
        }
    }
    false
}

} // verus!
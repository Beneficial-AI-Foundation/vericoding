use vstd::prelude::*;

fn main() {}

verus! {

fn contains_z(text: &[u8]) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 90 || text[i] == 122)),
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

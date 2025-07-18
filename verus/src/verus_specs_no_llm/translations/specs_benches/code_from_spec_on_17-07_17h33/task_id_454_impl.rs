use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 2): Fixed function signature by moving ensures clause inside function definition and removing duplicate return statement */
fn contains_z(text: &Vec<char>) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
{
    /* code modified by LLM (iteration 2): Added loop implementation with proper invariant to check for Z or z characters */
    for i in 0..text.len()
        invariant
            !(exists|j: int| 0 <= j < i && (text[j] == 'Z' || text[j] == 'z')),
    {
        if text[i] == 'Z' || text[i] == 'z' {
            return true;
        }
    }
    return false;
}

} // verus!

fn main() {}
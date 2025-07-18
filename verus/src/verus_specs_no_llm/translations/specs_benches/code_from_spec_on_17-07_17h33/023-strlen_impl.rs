use vstd::prelude::*;

verus! {

/* code modified by LLM (iteration 2): Fixed compilation errors by correcting function structure, placing ensures clause properly, and removing duplicate body */
fn strlen(string: &Vec<char>) -> (length: usize)
    ensures
        length == string.len(),
{
    string.len()
}

}
fn main() {}
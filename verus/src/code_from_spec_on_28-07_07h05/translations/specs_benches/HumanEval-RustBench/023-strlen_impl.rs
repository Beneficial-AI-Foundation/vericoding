use vstd::prelude::*;

verus! {

//IMPL strlen
fn strlen(string: &Vec<char>) -> (length: usize)
    // post-conditions-start
    ensures
        length == string.len(),
    // post-conditions-end
{
    string.len()
}

}
fn main() {}
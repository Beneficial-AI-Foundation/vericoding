use vstd::prelude::*;

verus! {

fn strlen(string: &Vec<char>) -> (length: usize)
    // post-conditions-start
    ensures
        length == string.len(),
    // post-conditions-end
{
    // impl-start
    string.len()
    // impl-end
}

}
fn main() {}
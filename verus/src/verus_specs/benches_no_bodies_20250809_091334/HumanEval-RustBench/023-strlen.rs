use vstd::prelude::*;

verus! {

fn strlen(string: &Vec<char>) -> (length: usize)
    // post-conditions-start
    ensures
        length == string.len(),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

}
fn main() {}

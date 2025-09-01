use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn strlen(string: &Vec<char>) -> (length: usize)
    // post-conditions-start
    ensures
        length == string.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    string.len()
}
// </vc-code>

fn main() {}
}
use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this simple implementation
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
    // impl-start
    string.len()
    // impl-end
}
// </vc-code>

fn main() {}
}
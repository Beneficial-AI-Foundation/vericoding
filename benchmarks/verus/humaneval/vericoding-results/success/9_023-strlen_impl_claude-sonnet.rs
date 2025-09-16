// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn strlen(string: &Vec<char>) -> (length: usize)

    ensures
        length == string.len(),
// </vc-spec>
// <vc-code>
{
    string.len()
}
// </vc-code>

}
fn main() {}
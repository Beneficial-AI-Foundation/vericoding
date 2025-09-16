// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_usize(x: usize) -> usize { x }
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
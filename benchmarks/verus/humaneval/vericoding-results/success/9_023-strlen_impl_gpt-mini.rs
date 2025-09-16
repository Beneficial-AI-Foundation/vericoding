// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn vec_len(v: &Vec<char>) -> usize { v.len() }
// </vc-helpers>

// <vc-spec>
fn strlen(string: &Vec<char>) -> (length: usize)

    ensures
        length == string.len(),
// </vc-spec>
// <vc-code>
{
    let length = string.len();
    length
}
// </vc-code>

}
fn main() {}
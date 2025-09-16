// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn strlen_trivial(s: &Vec<char>) ensures s.len() == s.len() { }
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
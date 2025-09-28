// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_z(text: &Vec<char>) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            !exists|j: int| 0 <= j < i && (text@[j] == 'Z' || text@[j] == 'z'),
        decreases text.len() - i
    {
        if text[i] == 'Z' || text[i] == 'z' {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}
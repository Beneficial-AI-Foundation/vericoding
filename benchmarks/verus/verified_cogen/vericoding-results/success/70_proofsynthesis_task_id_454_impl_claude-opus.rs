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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut i: usize = 0;
    let mut found = false;
    while i < text.len()
        invariant
            0 <= i <= text.len(),
            found == (exists|j: int| 0 <= j < i && (text[j] == 'Z' || text[j] == 'z')),
        decreases text.len() - i,
    {
        if text[i] == 'Z' || text[i] == 'z' {
            found = true;
            assert(exists|j: int| 0 <= j < i + 1 && (text[j] == 'Z' || text[j] == 'z'));
        }
        i = i + 1;
    }
    assert(i == text.len());
    assert(found == (exists|j: int| 0 <= j < text.len() && (text[j] == 'Z' || text[j] == 'z')));
    found
}
// </vc-code>

}
fn main() {}
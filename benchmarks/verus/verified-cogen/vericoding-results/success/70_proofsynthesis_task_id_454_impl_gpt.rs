// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): predicate to identify 'Z' or 'z' */
spec fn is_z(c: char) -> bool { c == 'Z' || c == 'z' }

/* helper modified by LLM (iteration 2): recursive search with proven postcondition */
fn contains_z_from(text: &Vec<char>, i: usize) -> (res: bool)
    requires
        i <= text.len()
    ensures
        res == (exists|j: int| i as int <= j < text.len() && (text[j] == 'Z' || text[j] == 'z'))
    decreases (text.len() as int) - (i as int)
{
    if i == text.len() {
        false
    } else {
        (text[i] == 'Z' || text[i] == 'z') || contains_z_from(text, i + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn contains_z(text: &Vec<char>) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): delegate to recursive helper to satisfy ensures */
    let result = contains_z_from(text, 0);
    result
}
// </vc-code>

}
fn main() {}
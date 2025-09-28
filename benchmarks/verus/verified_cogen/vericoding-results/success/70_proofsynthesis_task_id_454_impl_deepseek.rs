// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add exec while loop helper and fix proof helpers */
fn exec_find_z(text: &Vec<char>, mut i: usize) -> (result: bool)
    requires
        i <= text.len(),
    ensures
        result == (exists|j: int| i <= j < text.len() && (text@[j] == 'Z' || text@[j] == 'z')),
    decreases text.len() - i
{
    if i < text.len() {
        if text[i] == 'Z' || text[i] == 'z' {
            true
        } else {
            exec_find_z(text, i + 1)
        }
    } else {
        false
    }
}

proof fn find_z_index_recursive(text: &Vec<char>, start: int) -> (idx: int)
    requires
        0 <= start <= text.len(),
        exists|i: int| start <= i < text.len() && (text@[i] == 'Z' || text@[i] == 'z')
    ensures
        start <= idx < text.len() && (text@[idx] == 'Z' || text@[idx] == 'z')
    decreases text.len() - start
{
    if text@[start] == 'Z' || text@[start] == 'z' {
        start
    } else {
        find_z_index_recursive(text, start + 1)
    }
}

proof fn find_z_index(text: &Vec<char>) -> (idx: int)
    requires
        exists|i: int| 0 <= i < text.len() && (text@[i] == 'Z' || text@[i] == 'z')
    ensures
        0 <= idx < text.len() && (text@[idx] == 'Z' || text@[idx] == 'z')
{
    find_z_index_recursive(text, 0)
}
// </vc-helpers>

// <vc-spec>
fn contains_z(text: &Vec<char>) -> (result: bool)

    ensures
        result == (exists|i: int| 0 <= i < text.len() && (text[i] == 'Z' || text[i] == 'z')),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replace while loop with recursive exec function call */
{
    exec_find_z(text, 0)
}
// </vc-code>

}
fn main() {}
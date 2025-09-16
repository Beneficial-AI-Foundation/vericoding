// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Add decreases clause helper */
fn decreases_helper(n: usize) -> usize {
    n
}
// </vc-helpers>

// <vc-spec>
fn strlen(string: &Vec<char>) -> (length: usize)

    ensures
        length == string.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Add decreases clause to while loop */
    let mut i: usize = 0;
    while i < string.len()
        invariant
            i <= string.len(),
        decreases
            string.len() - i,
    {
        i = i + 1;
    }
    i
}
// </vc-code>

}
fn main() {}
// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helper functions are necessary */
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used ghost state for the original sequence to fix invariant logic */
    let ghost s_old = s@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == s_old.len(),
            forall|j: int| 0 <= j < i as int ==> s@[j] == 2 * s_old[j],
            forall|j: int| i as int <= j < s.len() as int ==> s@[j] == s_old[j],
        decreases s.len() - i
    {
        s[i] = 2 * s[i];
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}
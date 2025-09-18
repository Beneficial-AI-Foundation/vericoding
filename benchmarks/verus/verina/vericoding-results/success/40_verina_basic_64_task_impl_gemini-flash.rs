// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn insert(oline: &Vec<char>, l: usize, nl: &Vec<char>, p: usize, at_pos: usize) -> (result: Vec<char>)
    requires
        l <= oline.len(),
        p <= nl.len(),
        at_pos <= l,
    ensures
        result.len() == l + p,
        forall|i: int| 0 <= i < p ==> #[trigger] result[at_pos + i] == nl[i],
        forall|i: int| 0 <= i < at_pos ==> #[trigger] result[i] == oline[i],
        forall|i: int| 0 <= i < (l - at_pos) ==> #[trigger] result[at_pos + p + i] == oline[at_pos + i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed `oline.len()` access in first loop and improved invariants */
    let mut result_vec = Vec::new();
    let mut i = 0;

    while i < at_pos
        invariant
            0 <= i <= at_pos,
            result_vec.len() == i,
            // Ensure oline index is always valid
            at_pos <= oline.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec[j] == oline[j],
        decreases at_pos - i
    {
        result_vec.push(oline[i]);
        i += 1;
    }

    i = 0;
    while i < p
        invariant
            0 <= i <= p,
            result_vec.len() == at_pos + i,
            // Ensure nl index is always valid
            p <= nl.len(),
            forall|j: int| 0 <= j < at_pos ==> #[trigger] result_vec[j] == oline[j],
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec[at_pos + j] == nl[j],
        decreases p - i
    {
        result_vec.push(nl[i]);
        i += 1;
    }

    i = 0;
    while i < (l - at_pos)
        invariant
            0 <= i <= (l - at_pos),
            result_vec.len() == at_pos + p + i,
            // Ensure oline index is always valid at `at_pos + i`
            at_pos + (l - at_pos) <= oline.len(), // equivalent to l <= oline.len()
            forall|j: int| 0 <= j < at_pos ==> #[trigger] result_vec[j] == oline[j],
            forall|j: int| 0 <= j < p ==> #[trigger] result_vec[at_pos + j] == nl[j],
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec[at_pos + p + j] == oline[at_pos + j],
        decreases (l - at_pos) - i
    {
        result_vec.push(oline[at_pos + i]);
        i += 1;
    }

    result_vec
}
// </vc-code>

}
fn main() {}
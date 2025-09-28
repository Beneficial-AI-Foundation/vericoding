// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_length_list(lists: &Vec<Vec<int>>) -> (max_list: Vec<int>)
    requires lists.len() > 0
    ensures forall|i: int| 0 <= i < lists.len() ==> lists[i].len() <= max_list.len(),
            exists|i: int| 0 <= i < lists.len() && max_list@ == lists[i]@
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added an explicit assert to help the verifier prove the postconditions */
    let mut max_idx: usize = 0;
    let mut i: usize = 1;

    while i < lists.len()
        invariant
            1 <= i <= lists.len(),
            0 <= (max_idx as int) < (i as int),
            forall|j: int| 0 <= j < (i as int) ==> lists[j].len() <= lists[max_idx as int].len(),
        decreases lists.len() - i
    {
        if lists[i].len() > lists[max_idx].len() {
            max_idx = i;
        }
        i = i + 1;
    }

    let max_list = lists[max_idx].clone();

    // After the loop, the invariants hold with i = lists.len().
    // This proves `forall|j: int| 0 <= j < lists.len() ==> lists[j].len() <= max_list.len()`.
    // To prove the `exists` postcondition, we provide the witness `max_idx` to the verifier.
    // We know `0 <= (max_idx as int) < lists.len()` from the invariants.
    // We assert the equality, which helps instantiate the quantifier.
    assert(max_list@ == lists[max_idx as int]@);

    max_list
}
// </vc-code>

}
fn main() {}
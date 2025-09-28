// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): cast i to nat for use with Sequence.index */
fn count_true_in_condition(condition: &Vec<bool>) -> (count: nat)
    ensures
        count == (0..condition.len() as int).filter(|i: int| condition@.index(i)).count(),
{
    let mut count: nat = 0;
    let mut i: usize = 0;
    while i < condition.len()
        invariant
            0 <= i as int <= condition.len() as int,
            count == (0..i as int).filter(|j: int| condition@.index(j)).count(),
        decreases condition.len() - i
    {
        if condition@.index(i as nat) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-helpers>

// <vc-spec>
fn extract(condition: &Vec<bool>, arr: &Vec<i8>) -> (result: Vec<i8>)
    requires condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| 0 <= k < result@.len() ==>
            exists|i: int| 0 <= i < arr@.len() && condition@[i] == true && #[trigger] result@[k] == arr@[i],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| 0 <= i < condition@.len() && condition@[i] == true ==>
            exists|k: int| 0 <= k < result@.len() && #[trigger] result@[k] == arr@[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): cast i to nat for use with Sequence.index */
{
    let true_count = count_true_in_condition(condition);
    let mut result: Vec<i8> = Vec::with_capacity(true_count);

    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < condition.len()
        invariant
            0 <= i as int <= condition.len() as int,
            0 <= j as int <= result.len() as int,
            result.len() == (0..i as int).filter(|k: int| condition@.index(k)).count(),
            // All elements currently in `result` came from `arr` at positions where `condition` was true
            forall|k: int| 0 <= k < result@.len() ==> exists|idx: int| 0 <= idx < i as int && condition@.index(idx) && result@.index(k) == arr@.index(idx),
            // For all `true` conditions up to `i`, the corresponding `arr` element is in `result`
            forall|idx: int| 0 <= idx < i as int && condition@.index(idx) ==> exists|k: int| 0 <= k < result@.len() && result@.index(k) == arr@.index(idx),
        decreases condition.len() - i
    {
        if condition@.index(i as nat) {
            result.push(arr@.index(i as nat));
            j = j + 1;
        }
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}
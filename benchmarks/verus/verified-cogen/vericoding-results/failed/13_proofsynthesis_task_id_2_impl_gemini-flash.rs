// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn appears_in_both(list1: &Vec<i32>, list2: &Vec<i32>, elem: i32) -> bool { list1@.contains(elem) && list2@.contains(elem) }
// </vc-helpers>

// <vc-spec>
fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by adding curly braces for the last invariant. */
{
    let mut shared_vec: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < list1.len()
        invariant allows_alloc(),
        invariant 0 <= i,
        invariant i <= list1.len(),
        invariant forall|k: int| 0 <= k < shared_vec.len() ==> (appears_in_both(list1, list2, shared_vec@[k])),
        invariant forall|k: int, l: int| 0 <= k < l < shared_vec.len() ==> shared_vec@[k] != shared_vec@[l],
        invariant forall|elem: i32| {
            (!list1@.subsequence(0, i as int).contains(elem)) ==> !shared_vec@.contains(elem)
        }
    {
        let elem = list1@[i as int];
        if shared_vec.contains(&elem) {
            // Already added, skip
        } else if list2.contains(&elem) {
            shared_vec.push(elem);
        }
        i = i + 1;
    }
    shared_vec
}
// </vc-code>

}
fn main() {}
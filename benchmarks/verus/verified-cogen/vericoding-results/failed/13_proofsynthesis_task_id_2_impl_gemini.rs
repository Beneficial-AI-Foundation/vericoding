// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to prove termination */
fn contains(vec: &Vec<i32>, val: i32) -> (found: bool)
    ensures
        found == vec@.contains(val),
{
    let mut i: usize = 0;
    while i < vec.len()
        invariant
            i <= vec.len(),
            !vec@.subrange(0, i as int).contains(val),
        decreases vec.len() - i
    {
        if vec[i] == val {
            return true;
        }
        i = i + 1;
    }
    return false;
}
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
{
    /* code modified by LLM (iteration 2): added decreases clause to prove termination */
    let mut shared: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < list1.len()
        invariant
            i <= list1.len(),
            forall|k: int, j: int| 0 <= k < j < shared.len() ==> shared@[k] != shared@[j],
            forall|k: int| 0 <= k < shared.len() ==> list1@.subrange(0, i as int).contains(shared@[k]),
            forall|k: int| 0 <= k < shared.len() ==> list2@.contains(shared@[k]),
        decreases list1.len() - i
    {
        let element = list1[i];
        if contains(list2, element) && !contains(&shared, element) {
            shared.push(element);
        }
        i = i + 1;
    }
    shared
}
// </vc-code>

}
fn main() {}
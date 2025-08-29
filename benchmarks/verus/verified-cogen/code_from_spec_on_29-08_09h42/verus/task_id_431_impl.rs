use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    for i in 0..list1.len()
        invariant
            forall|k: int, j: int| 0 <= k < i && 0 <= j < list2.len() ==> list1[k] != list2[j]
    {
        for j in 0..list2.len()
            invariant
                /* code modified by LLM (iteration 3): fix bounds check for invariant */
                i < list1.len(),
                forall|k: int| 0 <= k < j ==> list1[i as int] != list2[k]
        {
            /* code modified by LLM (iteration 3): add bounds check before array access */
            if i < list1.len() && j < list2.len() && list1[i] == list2[j] {
                return true;
            }
        }
    }
    false
}
// </vc-code>

} // verus!

fn main() {}
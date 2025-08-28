use vstd::prelude::*;

verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
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
    let mut i: usize = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            forall|k: int| 0 <= k < i ==> !exists|m: int| 0 <= m < list2.len() && list1@[k as int] == list2@[m],
        decreases list1.len() - i
    {
        let mut j: usize = 0;
        while j < list2.len()
            invariant
                0 <= i < list1.len(),
                0 <= j <= list2.len(),
                forall|k: int| 0 <= k < i ==> !exists|m: int| 0 <= m < list2.len() && list1@[k as int] == list2@[m],
                !exists|m: int| 0 <= m < j && list1@[i as int] == list2@[m],
            decreases list2.len() - j
        {
            if list1[i] == list2[j] {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

} // verus!

fn main() {}
use vstd::prelude::*;


verus! {

// <vc-helpers>
// No changes needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    // pre-conditions-start
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
    // pre-conditions-end
// </vc-spec>

// <vc-code>
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr@[0] == #[trigger] arr@[i]),
{
    if arr@.len() == 0 {
        return true;
    }
    
    let mut i: usize = 1;
    while i < arr@.len()
        invariant
            1 <= i <= arr@.len(),
            forall|j: int| 1 <= j < i ==> arr@[0] == #[trigger] arr@[j],
    {
        if arr@[0] != arr@[i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

} // verus!

fn main() {}
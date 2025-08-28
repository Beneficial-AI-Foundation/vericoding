use vstd::prelude::*;


verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    // pre-conditions-start
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
    // pre-conditions-end
// </vc-spec>

// <vc-code>
{
    if arr.len() == 0 {
        return true;
    }
    
    let first_element = arr[0];
    let mut i = 1;
    
    while i < arr.len()
        invariant
            0 < arr@.len(),
            1 <= i <= arr@.len(),
            forall|j: int| 1 <= j < i ==> arr@[0] == #[trigger] arr@[j],
            arr@[0] == first_element,
        decreases arr@.len() - i
    {
        if arr[i] != first_element {
            proof {
                assert(arr@[0] == first_element);
                assert(arr@[i as int] != first_element);
                assert(arr@[0] != arr@[i as int]);
                assert(!(forall|k: int| 1 <= k < arr@.len() ==> arr@[0] == #[trigger] arr@[k]));
            }
            return false;
        }
        i += 1;
    }
    
    proof {
        assert(i == arr.len());
        assert(forall|j: int| 1 <= j < i ==> arr@[0] == #[trigger] arr@[j]);
        assert(forall|j: int| 1 <= j < arr@.len() ==> arr@[0] == #[trigger] arr@[j]);
    }
    
    true
}
// </vc-code>

} // verus!

fn main() {}
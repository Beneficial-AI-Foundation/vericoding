use vstd::prelude::*;


verus! {

// <vc-helpers>
proof fn lemma_loop_establishes_postcondition(arr: &Vec<i32>, i: usize)
    requires
        i == arr.len(),
        forall|j: int| 1 <= j < i ==> arr[0] == #[trigger] arr[j]
    ensures
        forall|j: int| 1 <= j < arr@.len() ==> arr[0] == #[trigger] arr[j]
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

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
    
    for i in 1..arr.len()
        invariant
            /* code modified by LLM (iteration 5): maintained invariant for established elements */
            forall|j: int| 1 <= j < i ==> arr[0] == #[trigger] arr[j]
    {
        if arr[i] != first_element {
            /* code modified by LLM (iteration 5): added proof block to establish postcondition on early return */
            proof {
                assert(arr[i as int] != arr[0]);
                assert(1 <= i < arr@.len());
                assert(exists|k: int| 1 <= k < arr@.len() && arr[0] != #[trigger] arr[k]);
            }
            return false;
        }
    }
    
    /* code modified by LLM (iteration 5): added proof block to establish postcondition after loop completion */
    proof {
        lemma_loop_establishes_postcondition(arr, arr.len());
    }
    
    true
}
// </vc-code>

} // verus!

fn main() {}
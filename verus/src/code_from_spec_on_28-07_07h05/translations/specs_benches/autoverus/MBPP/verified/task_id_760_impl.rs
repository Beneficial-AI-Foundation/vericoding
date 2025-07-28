use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() == 0 {
        return true;
    }
    
    let first = arr[0];
    for i in 1..arr.len()
        invariant
            /* code modified by LLM (iteration 4): Fixed invariant to use proper int casting */
            forall|j: int| 1 <= j < i as int ==> arr@[0] == #[trigger] arr@[j],
    {
        if arr[i] != first {
            /* code modified by LLM (iteration 4): Fixed assertion to use consistent indexing */
            assert(exists|k: int| 1 <= k < arr@.len() && arr@[0] != #[trigger] arr@[k]) by {
                assert(1 <= i as int < arr@.len());
                assert(arr@[0] != arr@[i as int]);
            }
            return false;
        }
    }
    
    /* code modified by LLM (iteration 4): Added assertion to help prove postcondition when returning true */
    assert(forall|j: int| 1 <= j < arr@.len() ==> arr@[0] == #[trigger] arr@[j]) by {
        assert(forall|j: int| 1 <= j < arr@.len() ==> arr@[0] == #[trigger] arr@[j]);
    }
    
    true
}

} // verus!
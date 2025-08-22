use vstd::prelude::*;

verus! {

//IMPL has_only_one_distinct_element
fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    // pre-conditions-start
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
    // pre-conditions-end
{
    if arr.len() == 0 {
        return true;
    }
    
    let first_element = arr[0];
    
    for i in 1..arr.len()
        invariant
            /* code modified by LLM (iteration 2): updated invariant to use first_element instead of arr[0] for clarity */
            forall|j: int| 1 <= j < i ==> first_element == #[trigger] arr[j],
    {
        if arr[i] != first_element {
            /* code modified by LLM (iteration 2): added assertion to prove postcondition when returning false */
            assert(arr[0] != arr[i as int]);
            /* code modified by LLM (iteration 3): added trigger annotation to fix compilation error */
            assert(!(forall|k: int| 1 <= k < arr@.len() ==> arr[0] == #[trigger] arr[k]));
            return false;
        }
        /* code modified by LLM (iteration 2): added assertion to help maintain loop invariant */
        assert(arr[i as int] == first_element);
    }
    
    /* code modified by LLM (iteration 4): added trigger annotation to fix compilation error */
    assert(forall|j: int| 1 <= j < arr@.len() ==> arr[0] == #[trigger] arr[j]);
    true
}

} // verus!

fn main() {}
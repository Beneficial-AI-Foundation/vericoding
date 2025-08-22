use vstd::prelude::*;

fn main() {}

verus! {

fn has_only_one_distinct_element(arr: &Vec<i32>) -> (result: bool)
    ensures
        result == (forall|i: int| 1 <= i < arr@.len() ==> arr[0] == #[trigger] arr[i]),
{
    if arr.len() == 0 {
        return true;
    }
    
    let first_element = arr[0];
    
    for i in 1..arr.len()
        invariant
            /* code modified by LLM (iteration 2): updated invariant to maintain loop bounds and element equality for checked indices */
            forall|j: int| 1 <= j < i ==> arr[0] == #[trigger] arr[j],
    {
        if arr[i] != first_element {
            /* code modified by LLM (iteration 3): added assertion with proper trigger annotation for exists quantifier */
            assert(arr[0] != arr[i as int]);
            assert(1 <= i < arr@.len());
            assert(exists|k: int| 1 <= k < arr@.len() && arr[0] != #[trigger] arr[k]);
            return false;
        }
    }
    
    /* code modified by LLM (iteration 4): added trigger annotation to fix automatic trigger inference error */
    assert(forall|j: int| 1 <= j < arr@.len() ==> arr[0] == #[trigger] arr[j]);
    true
}

} // verus!
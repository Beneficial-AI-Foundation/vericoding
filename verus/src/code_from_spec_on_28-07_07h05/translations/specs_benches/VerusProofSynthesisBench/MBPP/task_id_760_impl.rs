use vstd::prelude::*;

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
            /* code modified by LLM (iteration 4): updated invariant to use i as int and maintain loop property */
            forall|j: int| 1 <= j < i ==> arr[0] == #[trigger] arr[j],
    {
        if arr[i] != first {
            /* code modified by LLM (iteration 4): added assertion to prove postcondition when returning false */
            assert(arr[0] != arr[i as int]);
            assert(1 <= i < arr@.len());
            assert(exists|k: int| 1 <= k < arr@.len() && arr[0] != #[trigger] arr[k]);
            return false;
        }
        /* code modified by LLM (iteration 4): added assertion to help maintain loop invariant */
        assert(arr[0] == arr[i as int]);
    }
    /* code modified by LLM (iteration 4): added assertion to prove postcondition when returning true */
    assert(forall|j: int| 1 <= j < arr@.len() ==> arr[0] == #[trigger] arr[j]);
    true
}

} // verus!

fn main() {}
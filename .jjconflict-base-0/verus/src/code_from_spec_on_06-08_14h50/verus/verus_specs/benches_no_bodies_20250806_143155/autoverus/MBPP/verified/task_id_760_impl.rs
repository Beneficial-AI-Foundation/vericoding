use vstd::prelude::*;

fn main() {
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
    let mut idx = 1;
    
    /* code modified by LLM (iteration 1): added trigger annotation to loop invariant quantifier */
    while idx < arr.len()
        invariant
            1 <= idx <= arr.len(),
            forall|j: int| 1 <= j < idx ==> arr[0] == #[trigger] arr[j],
        decreases arr.len() - idx
    {
        if arr[idx] != first {
            return false;
        }
        idx += 1;
    }
    
    true
}

} // verus!
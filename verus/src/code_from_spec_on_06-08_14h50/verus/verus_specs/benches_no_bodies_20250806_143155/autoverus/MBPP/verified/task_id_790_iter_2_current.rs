use vstd::prelude::*;

fn main() {
}

verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < arr.len()
        invariant
            0 <= idx <= arr.len(),
            forall|i: int| 0 <= i < idx ==> ((i % 2) == (arr[i] % 2)),
        decreases arr.len() - idx,
    {
        if (idx % 2) != (arr[idx] % 2) {
            return false;
        }
        idx += 1;
    }
    
    true
}

} // verus!
use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn is_odd_at_odd_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut idx: usize = 0;
    while idx < arr.len()
        invariant
            0 <= idx <= arr.len(),
            forall|i: int| 0 <= i < idx ==> ((i % 2) == (arr[i] % 2)),
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases arr.len() - idx,
    {
        if (idx % 2) != (arr[idx] % 2) {
            return false;
        }
        idx = idx + 1;
    }
    true
}

} // verus!
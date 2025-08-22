use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    let mut index = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> ((i % 2) == (arr[i] % 2)),
        decreases arr.len() - index,
    {
        if (index % 2) != (arr[index] % 2) {
            return false;
        }
        index += 1;
    }
    
    true
}

} // verus!
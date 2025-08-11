use vstd::prelude::*;

fn main() {}

verus! {

fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut index = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix termination checking */
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|i: int| 0 <= i < index ==> number > arr[i],
        decreases arr.len() - index,
    {
        if number <= arr[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!
use vstd::prelude::*;

fn main() {}

verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> ((j % 2) == (arr[j] % 2)),
    {
        if (i % 2) != (arr[i] % 2) {
            return false;
        }
    }
    true
}

} // verus!
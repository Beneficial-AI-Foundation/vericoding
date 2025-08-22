use vstd::prelude::*;

fn main() {}

verus! {

fn is_even_at_even_index(arr: &Vec<usize>) -> (result: bool)
    ensures
        result == forall|i: int| 0 <= i < arr.len() ==> ((i % 2) == (arr[i] % 2)),
{
    for idx in 0..arr.len()
        invariant forall|i: int| 0 <= i < idx ==> ((i % 2) == (arr[i] % 2))
    {
        if (idx % 2) != (arr[idx] % 2) {
            return false;
        }
    }
    true
}

} // verus!
use vstd::prelude::*;

fn main() {}

verus! {

fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    for i in 0..arr.len()
        invariant forall|j: int| 0 <= j < i ==> number > arr[j]
    {
        if number <= arr[i] {
            return false;
        }
    }
    true
}

} // verus!
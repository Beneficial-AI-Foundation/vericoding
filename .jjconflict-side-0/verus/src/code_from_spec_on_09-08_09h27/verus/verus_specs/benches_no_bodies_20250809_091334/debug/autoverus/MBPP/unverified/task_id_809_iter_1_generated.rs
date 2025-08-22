use vstd::prelude::*;

fn main() {}

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut j = 0;
    
    while j < arr1.len()
        invariant
            0 <= j <= arr1.len(),
            forall|i: int| 0 <= i < j ==> arr1[i] > arr2[i],
    {
        if arr1[j] <= arr2[j] {
            return false;
        }
        j += 1;
    }
    
    true
}

} // verus!
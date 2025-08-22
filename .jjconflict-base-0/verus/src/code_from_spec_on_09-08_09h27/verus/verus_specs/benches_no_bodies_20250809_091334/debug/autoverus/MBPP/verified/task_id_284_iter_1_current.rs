use vstd::prelude::*;

fn main() {
}

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[j] == element,
    {
        if arr[i] != element {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!
use vstd::prelude::*;

fn main() {
    // Example usage of all_elements_equals
    let vec1 = vec![5, 5, 5, 5];
    let vec2 = vec![1, 2, 3, 4];
    
    println!("All elements in vec1 equal 5: {}", all_elements_equals(&vec1, 5));
    println!("All elements in vec2 equal 1: {}", all_elements_equals(&vec2, 1));
}

verus! {

fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
{
    for i in 0..arr.len()
        invariant forall|j: int| 0 <= j < i ==> arr[j] == element
    {
        if arr[i] != element {
            return false;
        }
    }
    true
}

} // verus!
use vstd::prelude::*;

fn main() {
    // Example usage
    let arr1 = vec![5, 3, 8];
    let arr2 = vec![2, 1, 6];
    let result = is_smaller(&arr1, &arr2);
    println!("Result: {}", result);
}

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut index = 0;
    
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            forall|i: int| 0 <= i < index ==> arr1[i] > arr2[i],
    {
        if arr1[index] <= arr2[index] {
            return false;
        }
        index = index + 1;
    }
    
    true
}

} // verus!
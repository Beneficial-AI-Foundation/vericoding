use vstd::prelude::*;

fn main() {
    let arr = vec![1, 2, 3, 4, 5];
    let result = is_greater(&arr, 10);
    println!("Is 10 greater than all elements? {}", result);
}

verus! {

fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut idx = 0;
    
    while idx < arr.len()
        invariant
            0 <= idx <= arr.len(),
            forall|i: int| 0 <= i < idx ==> number > arr[i],
    {
        if number <= arr[idx] {
            return false;
        }
        idx += 1;
    }
    
    true
}

} // verus!
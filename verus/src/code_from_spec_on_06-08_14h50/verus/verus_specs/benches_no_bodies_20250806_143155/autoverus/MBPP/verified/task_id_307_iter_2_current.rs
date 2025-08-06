use vstd::prelude::*;

fn main() {
    let original = vec![1, 2, 3, 4, 5];
    let cloned = list_deep_clone(&original);
    println!("Original: {:?}", original);
    println!("Cloned: {:?}", cloned);
}

verus! {

fn list_deep_clone(arr: &Vec<u64>) -> (copied: Vec<u64>)
    ensures
        arr@.len() == copied@.len(),
        forall|i: int| (0 <= i < arr.len()) ==> arr[i] == copied[i],
{
    let mut copied = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix loop verification */
    while idx < arr.len()
        invariant
            idx <= arr.len(),
            copied@.len() == idx,
            forall|j: int| (0 <= j < idx) ==> arr[j] == copied[j],
        decreases arr.len() - idx
    {
        copied.push(arr[idx]);
        idx += 1;
    }
    
    copied
}

} // verus!
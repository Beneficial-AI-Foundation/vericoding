use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
    {
        if arr[i] == key {
            return true;
        }
    }
    false
}

fn intersection(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let mut result = Vec::new();
    
    for i in 0..arr1.len()
        invariant
            forall|k: int|
                0 <= k < result.len() ==> (arr1@.contains(#[trigger] result[k]) && arr2@.contains(
                    #[trigger] result[k],
                )),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
    {
        let element = arr1[i];
        
        // Check if element is in arr2
        let mut found_in_arr2 = false;
        for j in 0..arr2.len()
            invariant
                found_in_arr2 == (exists|k: int| 0 <= k < j && arr2[k] == element),
        {
            if arr2[j] == element {
                found_in_arr2 = true;
                break;
            }
        }
        
        if found_in_arr2 {
            // Check if element is already in result
            let mut already_added = false;
            for k in 0..result.len()
                invariant
                    already_added == (exists|m: int| 0 <= m < k && result[m] == element),
            {
                if result[k] == element {
                    already_added = true;
                    break;
                }
            }
            
            if !already_added {
                result.push(element);
            }
        }
    }
    
    result
}

} // verus!
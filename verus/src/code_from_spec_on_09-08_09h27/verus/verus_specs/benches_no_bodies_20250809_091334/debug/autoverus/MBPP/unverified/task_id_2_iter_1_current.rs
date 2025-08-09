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

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut result = Vec::new();
    
    for i in 0..list1.len()
        invariant
            forall|k: int|
                0 <= k < result.len() ==> (list1@.contains(result[k]) && list2@.contains(result[k])),
            forall|k1: int, k2: int| 0 <= k1 < k2 < result.len() ==> result[k1] != result[k2],
    {
        let elem = list1[i];
        
        // Check if elem is in list2
        let mut found_in_list2 = false;
        for j in 0..list2.len()
            invariant
                found_in_list2 == (exists|k: int| 0 <= k < j && list2[k] == elem),
        {
            if list2[j] == elem {
                found_in_list2 = true;
            }
        }
        
        if found_in_list2 {
            // Check if elem is already in result
            let mut already_added = false;
            for k in 0..result.len()
                invariant
                    already_added == (exists|m: int| 0 <= m < k && result[m] == elem),
            {
                if result[k] == elem {
                    already_added = true;
                }
            }
            
            if !already_added {
                result.push(elem);
            }
        }
    }
    
    result
}

} // verus!
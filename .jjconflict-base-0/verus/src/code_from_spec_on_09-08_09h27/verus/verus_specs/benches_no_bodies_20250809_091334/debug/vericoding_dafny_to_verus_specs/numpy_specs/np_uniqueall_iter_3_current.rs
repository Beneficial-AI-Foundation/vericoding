use vstd::prelude::*;

verus! {

fn unique_all(arr: &[i32]) -> (ret: Vec<i32>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> exists|j: int| 0 <= j < ret.len() && #[trigger] ret[j] == #[trigger] arr[i],
        forall|i: int, j: int| 0 <= i < ret.len() && 0 <= j < i ==> ret[i] != ret[j],
{
    let mut result = Vec::new();
    
    for i in 0..arr.len()
        invariant
            result.len() <= i,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < result.len() && result[j] == arr[k],
            forall|p: int, q: int| 0 <= p < result.len() && 0 <= q < p ==> result[p] != result[q],
    {
        let mut found = false;
        
        for j in 0..result.len()
            invariant
                /* code modified by LLM (iteration 1): use usize directly instead of int conversion for array indexing */
                forall|k: int| 0 <= k < j ==> result[k] != arr[i as int],
                found == exists|k: int| 0 <= k < j && result[k] == arr[i as int],
        {
            /* code modified by LLM (iteration 1): use usize directly instead of int conversion for array indexing */
            if result[j] == arr[i] {
                found = true;
                break;
            }
        }
        
        if !found {
            /* code modified by LLM (iteration 1): use usize directly instead of int conversion for array indexing */
            result.push(arr[i]);
        }
    }
    
    result
}

}

fn main() {}
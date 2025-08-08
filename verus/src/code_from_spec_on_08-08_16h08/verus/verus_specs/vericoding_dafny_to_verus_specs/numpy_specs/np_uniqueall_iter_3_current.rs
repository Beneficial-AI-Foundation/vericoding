use vstd::prelude::*;

verus! {

fn unique_all(arr: &[i32]) -> (ret: Vec<i32>)
    ensures
        ret.len() <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> exists|j: int| 0 <= j < ret.len() && #[trigger] ret[j] == #[trigger] arr[i],
        forall|i: int, j: int| 0 <= i < ret.len() && 0 <= j < i ==> ret[i] != ret[j],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): added trigger annotations to fix quantifier inference */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            result.len() <= i,
            forall|k: int| 0 <= k < i ==> exists|j: int| 0 <= j < result.len() && #[trigger] result[j] == #[trigger] arr[k],
            forall|p: int, q: int| 0 <= p < result.len() && 0 <= q < p ==> result[p] != result[q],
        decreases arr.len() - i
    {
        let current = arr[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found ==> exists|k: int| 0 <= k < j && result[k] == current,
                !found ==> forall|k: int| 0 <= k < j ==> result[k] != current,
            decreases result.len() - j
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            result.push(current);
        }
        
        i += 1;
    }
    
    result
}

}

fn main() {}
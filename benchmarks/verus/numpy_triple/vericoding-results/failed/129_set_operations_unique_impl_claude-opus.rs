// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn contains(v: Vec<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < v.len() && v[i] == x
}

proof fn lemma_insert_maintains_sorted(v: Vec<i32>, x: i32, pos: int)
    requires
        0 <= pos <= v.len(),
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] < v[j],
        forall|i: int| 0 <= i < pos ==> v[i] < x,
        forall|i: int| pos <= i < v.len() ==> x < v[i],
    ensures
        forall|i: int, j: int| #![trigger v[i], v[j]] 0 <= i < j < v.len() + 1 ==> 
            if i < pos && j < pos { v[i] < v[j] }
            else if i < pos && j == pos { v[i] < x }
            else if i < pos && j > pos { v[i] < v[j-1] }
            else if i == pos && j > pos { x < v[j-1] }
            else if i > pos && j > pos { v[i-1] < v[j-1] }
            else { true }
{
}
// </vc-helpers>

// <vc-spec>
fn unique(arr: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> result[i] < result[j],

        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> exists|j: int| 0 <= j < arr.len() && result[i] == arr[j],

        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> result[i] != result[j],

        forall|i: int| #![trigger arr[i]] 0 <= i < arr.len() ==> exists|j: int| 0 <= j < result.len() && arr[i] == result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger annotation by using trigger on exists */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int, k: int| #![auto] 0 <= j < k < result.len() ==> result[j] < result[k],
            forall|j: int| #![trigger result[j]] 0 <= j < result.len() ==> exists|k: int| 0 <= k < i && result[j] == arr[k],
            forall|j: int, k: int| #![auto] 0 <= j < result.len() && 0 <= k < result.len() && j != k ==> result[j] != result[k],
            forall|j: int| #![auto] 0 <= j < i ==> exists|k: int| 0 <= k < result.len() && arr[j] == result[k],
        decreases arr.len() - i
    {
        let val = arr[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                !found ==> forall|k: int| #![auto] 0 <= k < j ==> result[k] != val,
                found ==> exists|k: int| 0 <= k < j && result[k] == val,
            decreases result.len() - j
        {
            if result[j] == val {
                found = true;
                break;
            }
            j = j + 1;
        }
        
        if !found {
            let mut insert_pos = 0;
            while insert_pos < result.len()
                invariant
                    0 <= insert_pos <= result.len(),
                    forall|k: int| #![auto] 0 <= k < insert_pos ==> result[k] < val,
                decreases result.len() - insert_pos
            {
                if result[insert_pos] > val {
                    break;
                }
                insert_pos = insert_pos + 1;
            }
            
            result.insert(insert_pos, val);
            proof {
                lemma_insert_maintains_sorted(result, val, insert_pos as int);
            }
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
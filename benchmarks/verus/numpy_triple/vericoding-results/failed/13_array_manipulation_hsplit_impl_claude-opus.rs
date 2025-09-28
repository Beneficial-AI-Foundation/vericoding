// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hsplit(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires 
        k > 0,
        arr@.len() % (k as nat) == 0,
    ensures
        result@.len() == k,
        forall|part_idx: int| 0 <= part_idx < k as int ==> result@[part_idx].len() == arr@.len() / (k as nat),
        forall|part_idx: int, elem_idx: int| 
            0 <= part_idx < k as int && 0 <= elem_idx < (arr@.len() / (k as nat)) as int ==>
            #[trigger] result@[part_idx][elem_idx] == arr@[part_idx * ((arr@.len() / (k as nat)) as int) + elem_idx],
        forall|i: int| 0 <= i < arr@.len() ==> 
            exists|p: int, e: int| 
                0 <= p < k as int && 0 <= e < (arr@.len() / (k as nat)) as int &&
                i == p * ((arr@.len() / (k as nat)) as int) + e &&
                #[trigger] arr@[i] == result@[p][e]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed arithmetic overflow and bounds checking */
    let part_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    
    while i < k
        invariant
            k > 0,
            arr@.len() % (k as nat) == 0,
            part_size == arr.len() / k,
            part_size > 0,
            i <= k,
            result@.len() == i,
            i * part_size <= arr.len(),
            forall|part_idx: int| 0 <= part_idx < i as int ==> result@[part_idx].len() == part_size,
            forall|part_idx: int, elem_idx: int| 
                0 <= part_idx < i as int && 0 <= elem_idx < part_size as int ==>
                part_idx * part_size as int + elem_idx < arr@.len() &&
                #[trigger] result@[part_idx][elem_idx] == arr@[part_idx * part_size as int + elem_idx]
        decreases k - i
    {
        let mut part: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        let start: usize = i * part_size;
        
        while j < part_size
            invariant
                k > 0,
                arr@.len() % (k as nat) == 0,
                part_size == arr.len() / k,
                part_size > 0,
                i < k,
                start == i * part_size,
                start + part_size <= arr.len(),
                j <= part_size,
                part@.len() == j,
                forall|elem_idx: int| 0 <= elem_idx < j as int ==>
                    start as int + elem_idx < arr@.len() &&
                    #[trigger] part@[elem_idx] == arr@[start as int + elem_idx]
            decreases part_size - j
        {
            part.push(arr[start + j]);
            j = j + 1;
        }
        
        result.push(part);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}
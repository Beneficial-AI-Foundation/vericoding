// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by removing 'lemma' keyword */
fn bounds_for_hsplit_index(arr_len: nat, k: nat, i: nat, j: nat)
    requires
        k > 0,
        arr_len % k == 0,
        i < k,
        j < arr_len / k,
    ensures
        i * (arr_len / k) + j < arr_len,
{
    assert(arr_len == k * (arr_len / k));
    assert(i * (arr_len / k) + j < (i + 1) * (arr_len / k));
    assert((i + 1) * (arr_len / k) <= k * (arr_len / k));
}
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
    /* code modified by LLM (iteration 5): added bounds checking with helper lemma */
    let chunk_size = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i = 0;
    
    while i < k
        invariant
            i <= k,
            result@.len() == i,
            chunk_size == arr@.len() / (k as nat),
            forall|part_idx: int| 0 <= part_idx < i as int ==> #[trigger] result@[part_idx].len() == chunk_size,
            forall|part_idx: int, elem_idx: int| 
                0 <= part_idx < i as int && 0 <= elem_idx < chunk_size as int ==>
                part_idx * (chunk_size as int) + elem_idx < arr@.len() &&
                #[trigger] result@[part_idx][elem_idx] == arr@[part_idx * (chunk_size as int) + elem_idx]
        decreases k - i
    {
        let mut chunk: Vec<f32> = Vec::new();
        let mut j = 0;
        
        while j < chunk_size
            invariant
                j <= chunk_size,
                chunk@.len() == j,
                i < k,
                chunk_size == arr@.len() / (k as nat),
                forall|elem_idx: int| 
                    0 <= elem_idx < j as int ==>
                    (i as int) * (chunk_size as int) + elem_idx < arr@.len() &&
                    #[trigger] chunk@[elem_idx] == arr@[(i as int) * (chunk_size as int) + elem_idx]
            decreases chunk_size - j
        {
            proof {
                bounds_for_hsplit_index(arr@.len(), k as nat, i as nat, j as nat);
            }
            chunk.push(arr[i * chunk_size + j]);
            j += 1;
        }
        
        result.push(chunk);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}
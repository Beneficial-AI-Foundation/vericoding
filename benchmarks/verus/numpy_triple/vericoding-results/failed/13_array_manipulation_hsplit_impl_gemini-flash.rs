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
    /* code modified by LLM (iteration 5): [Fixed type issues by only casting to `int` when directly indexing the ghost sequence `arr@`.] */
    let sub_array_len: usize = arr@.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut part_idx: usize = 0;

    while part_idx < k
        invariant
            result@.len() == part_idx,
            forall|i: int| 0 <= i < part_idx as int ==> result@[i].len() == sub_array_len as nat,
            forall|p_idx: int, e_idx: int|
                0 <= p_idx < part_idx as int && 0 <= e_idx < sub_array_len as int ==> 
                #[trigger] result@[p_idx][e_idx] == arr@[p_idx * sub_array_len as int + e_idx],
            arr@.len() % (k as nat) == 0,
            k > 0,
            part_idx <= k,
        decreases k - part_idx
    {
        let mut current_part: Vec<f32> = Vec::new();
        let mut elem_idx: usize = 0;

        while elem_idx < sub_array_len
            invariant
                current_part@.len() == elem_idx,
                forall|i_idx: int| 0 <= i_idx < elem_idx as int ==> 
                    current_part@[i_idx] == arr@[ (part_idx as int * sub_array_len as int + i_idx as int) ],
                part_idx < k,
                elem_idx <= sub_array_len,
            decreases sub_array_len - elem_idx
        {
            current_part.push(arr@[ (part_idx as int * sub_array_len as int + elem_idx as int) ]);
            elem_idx = elem_idx + 1;
        }
        result.push(current_part);
        part_idx = part_idx + 1;
    }
    result
}
// </vc-code>


}
fn main() {}
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
/* code modified by LLM (iteration 5): Fixed compilation error by using usize for executable variables instead of spec types like int and nat */
{
    let part_size: usize = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            result@.len() == {i as nat},
            forall|idx: int| 0 <= idx < {i as nat} ==> result@[idx].len() == {part_size as nat},
        decreases ({k as nat} - {i as nat})
    {
        let mut part: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < part_size
            invariant
                part@.len() == {j as nat},
            decreases ({part_size as nat} - {j as nat})
        {
            part.push(arr[i * part_size + j]);
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
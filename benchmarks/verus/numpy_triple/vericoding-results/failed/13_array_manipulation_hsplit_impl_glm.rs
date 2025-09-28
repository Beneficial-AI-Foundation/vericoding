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
    /* code modified by LLM (iteration 5): fixed compilation errors by replacing int with usize in executable code and converting to int only in ghost contexts */
    let part_len: usize = arr.len() / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i as int <= k as int,
            result@.len() == i as int,
            forall|part_idx: int| 0 <= part_idx < i as int ==> result@[part_idx].len() == part_len as int,
            forall|part_idx: int, elem_idx: int| 
                0 <= part_idx < i as int && 0 <= elem_idx < part_len as int ==>
                #[trigger] result@[part_idx][elem_idx] == arr@[part_idx * (part_len as int) + elem_idx],
            forall|idx: int| 
                0 <= idx < (i as int) * (part_len as int) ==>
                exists|p: int, e: int| 
                    0 <= p < i as int && 0 <= e < part_len as int &&
                    idx == p * (part_len as int) + e &&
                    #[trigger] arr@[idx] == result@[p][e]
        decreases (k - i) as nat
    {
        let start: usize = i * part_len;
        let end: usize = start + part_len;
        proof {
            assert(i as int >= 0);
            assert(part_len as int >= 0);
            assert(start as int >= 0);
            assert(end as int <= (k as int) * (part_len as int));
            assert((k as int) * (part_len as int) == arr@.len() as int);
            assert(end as int <= arr@.len() as int);
        }
        let mut part = Vec::new();
        let mut j: usize = start;
        while j < end
            invariant
                start as int <= j as int <= end as int,
                part@.len() == (j - start) as int,
                forall|idx: int| start as int <= idx < j as int ==> part@[idx - (start as int)] == arr@[idx]
            decreases (end - j) as nat
        {
            part.push(arr[j]);
            j += 1;
        }
        result.push(part);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}
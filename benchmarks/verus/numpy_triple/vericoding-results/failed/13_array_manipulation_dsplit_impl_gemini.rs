// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn dsplit(arr: Vec<f32>, sections: usize) -> (result: Vec<Vec<f32>>)
    requires 
        sections > 0,
        arr.len() % sections == 0,
    ensures
        result.len() == sections,
        forall|i: int| 0 <= i < sections ==> result[i].len() == arr.len() / sections,
        forall|i: int, j: int| 0 <= i < sections && 0 <= j < (arr.len() / sections) ==> 
            result[i][j] == arr[i * (arr.len() / sections) + j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed 'invariant' syntax, used spec accessors (.view()), and added proof hints */
    let chunk_size = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i: usize = 0;
    while i < sections
        decreases sections - i
        invariant
            0 <= i <= sections,
            chunk_size == arr.len() / sections,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result.view()[k].len() == chunk_size,
            forall|k: int, j: int|
                0 <= k < i && 0 <= j < (chunk_size as int) ==> 
                #[trigger] result.view()[k].view()[j] == arr.view()[k * (chunk_size as int) + j]
    {
        let start = i * chunk_size;
        let end = (i + 1) * chunk_size;

        let sub_seq = arr.view().subrange(start as int, end as int);
        let sub_vec = sub_seq.to_vec();
        
        proof {
            sub_seq.to_vec_ensures(); // Links sub_vec.view() to sub_seq for the verifier
        }

        result.push(sub_vec);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}
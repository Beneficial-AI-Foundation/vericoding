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
/* code modified by LLM (iteration 4): fixed type annotation for result vector */
{
    let chunk_size = arr.len() / sections;
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(sections);
    for i in 0..sections
        invariant
            result.len() == i,
            (i+1) * chunk_size <= arr.len(),
            forall|k: int| 0 <= k < i ==> result[k].len() == chunk_size,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < chunk_size ==> result[k][l] == arr[k * chunk_size + l],
    {
        let start = i * chunk_size;
        let mut chunk = Vec::with_capacity(chunk_size);
        for j in 0..chunk_size
            invariant
                chunk.len() == j,
                forall|l: int| 0 <= l < j ==> chunk[l] == arr[start + l],
        {
            chunk.push(arr[start + j]);
        }
        result.push(chunk);
    }
    result
}
// </vc-code>

}
fn main() {}
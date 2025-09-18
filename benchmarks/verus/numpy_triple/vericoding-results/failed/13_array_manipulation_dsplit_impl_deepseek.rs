// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn chunk_size(total: usize, sections: usize) -> usize
    requires sections > 0,
    ensures result == total / sections,
{
    total / sections
}

proof fn indexing_lemma(arr: &Vec<f32>, chunk: usize, i: usize, j: usize)
    requires
        arr.len() % chunk == 0,
        i < arr.len() / chunk,
        j < chunk,
    ensures
        #[trigger] arr@.index(i * chunk + j) == arr@[i * chunk + j],
{
}

/* helper modified by LLM (iteration 5): Fixed ensures clause to use proper return value binding */
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
    /* code modified by LLM (iteration 5): Fixed result variable declaration and ensures clause */
    let len = arr.len();
    let chunk_size_val = chunk_size(len, sections);
    let mut result_vec = Vec::new();
    let mut i = 0;
    while i < sections
        invariant
            0 <= i <= sections,
            result_vec.len() == i,
            forall|k: int| 0 <= k < i ==> result_vec[k as usize].len() == chunk_size_val,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < chunk_size_val ==> 
                result_vec[k as usize][l] == arr@[k * chunk_size_val + l],
    {
        let mut chunk_vec = Vec::new();
        let mut j = 0;
        while j < chunk_size_val
            invariant
                0 <= j <= chunk_size_val,
                chunk_vec.len() == j,
                forall|l: int| 0 <= l < j ==> chunk_vec[l] == arr@[i * chunk_size_val + l],
        {
            let index = i * chunk_size_val + j;
            proof { indexing_lemma(&arr, chunk_size_val, i, j); }
            chunk_vec.push(arr[index]);
            j += 1;
        }
        result_vec.push(chunk_vec);
        i += 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}
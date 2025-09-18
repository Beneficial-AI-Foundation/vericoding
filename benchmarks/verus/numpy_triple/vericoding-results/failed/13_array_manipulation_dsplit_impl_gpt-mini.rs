// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): integer helpers for chunk length and flat index */
spec fn chunk_len(arr_len: int, sections: int) -> int { arr_len / sections }
spec fn flat_index(i: int, j: int, chunk: int) -> int { i * chunk + j }
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
    /* code modified by LLM (iteration 5): imperative splitting with loop invariants avoiding '<=' syntax */
    let n: usize = arr.len();
    let chunk: usize = n / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < sections {
        invariant i < sections + 1;
        invariant result.len() == i;
        invariant forall |ii: int| 0 <= ii && ii < i as int ==>
            result[ii as usize].len() == chunk &&
            forall |jj: int| 0 <= jj && jj < chunk as int ==>
                result[ii as usize][jj as usize] == arr[(ii as usize) * chunk + jj as usize];
        let mut v: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < chunk {
            invariant j < chunk + 1;
            invariant v.len() == j;
            invariant forall |jj: int| 0 <= jj && jj < j as int ==>
                v[jj as usize] == arr[i * chunk + jj as usize];
            v.push(arr[i * chunk + j]);
            j += 1;
        }
        result.push(v);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
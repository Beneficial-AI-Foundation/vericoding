// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): utility for computing chunk length as a spec */
spec fn chunk_len(n: nat, s: nat) -> nat { n / s }
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
    /* code modified by LLM (iteration 4): build result using nested loops over sections and per-chunk elements */
    let chunk: usize = arr.len() / sections;

    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < sections
        invariant
            result.len() == i,
            // established rows have correct length
            forall|ii: int| 0 <= ii && ii < i as int ==> result@[ii].len() == chunk as int,
            // established rows have correct contents
            forall|ii: int, jj: int|
                0 <= ii && ii < i as int && 0 <= jj && jj < chunk as int ==>
                    result@[ii]@[(jj)] == arr@[(((ii * (chunk as int)) + jj))],
        decreases sections - i
    {
        let mut inner: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < chunk
            invariant
                inner.len() == j,
                // elements copied so far match arr at the correct flattened indices for this row
                forall|jj: int| 0 <= jj && jj < j as int ==> inner@[(jj)] == arr@[(((i as int) * (chunk as int)) + jj)],
            decreases chunk - j
        {
            let idx = i * chunk + j;
            let v = arr[idx];
            inner.push(v);
            j += 1;
        }
        // inner row completed and matches arr for row i by the inner-loop invariant
        result.push(inner);
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}
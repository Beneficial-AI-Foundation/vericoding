// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The helper section was empty, so it's kept empty. */
// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<Vec<i32>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i] * b[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `a[i]` to `a@[i]` to fix type mismatch. */
{
    let mut result: Vec<Vec<i32>> = Vec::new();
    assert!(result.len() == 0);

    let a_len = a.len();
    let b_len = b.len();

    // Loop for `i`
    for i in 0..a_len
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == b_len,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < b_len ==> result[k][l] == a@[k] * b@[l],
    {
        let mut row: Vec<i32> = Vec::new();
        assert!(row.len() == 0);

        // Loop for `j`
        for j in 0..b_len
            invariant
                row.len() == j,
                forall|l: int| 0 <= l < j ==> row[l] == a@[i] * b@[l],
        {
            row.push(a@[i] * b@[j]);
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}
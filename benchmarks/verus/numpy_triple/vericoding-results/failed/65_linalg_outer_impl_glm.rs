// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 2): fixed type annotation and index conversion */
    let mut result: Vec<Vec<i32>> = Vec::new();
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|ii: int| 0 <= ii < result.len() ==> result[ii].len() == b.len(),
            forall|ii: int, j: int| 0 <= ii < result.len() && 0 <= j < result[ii].len() ==> 
                result[ii][j] == a[ii] * b[j]
    {
        let mut row = Vec::new();
        for j in 0..b.len()
            invariant
                row.len() == j,
                forall|k: int| 0 <= k < row.len() ==> row[k] == a[i as int] * b[k]
        {
            row.push(a[i] * b[j]);
        }
        result.push(row);
    }
    result
}
// </vc-code>

}
fn main() {}
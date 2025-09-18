// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn fliplr(m: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        m.len() > 0,
        forall|i: int| 0 <= i < m.len() ==> m[i].len() > 0,
        forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m[i].len() == m[j].len(),
    ensures
        result.len() == m.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m[i].len(),
        forall|i: int, j: int| #![trigger result[i][j]] 0 <= i < result.len() && 0 <= j < result[i].len() ==>
            result[i][j] == m[i][(m[i].len() - 1 - j as usize) as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches by consistently using `usize` for array indexing within invariants and ensuring `cols` is passed as `int` where required by `forall` quantifiers.*/
{
    let rows = m.len();
    let cols = m[0].len();
    let mut result: Vec<Vec<f32>> = Vec::new();

    let mut i = 0;
    while i < rows
        invariant
            0 <= i && i <= rows,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k].len() == cols,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < cols ==> result[k][l] == m[k].get((cols - 1 - l) as usize).unwrap(),
    {
        let mut new_row: Vec<f32> = Vec::new();
        let mut j = 0;
        while j < cols
            invariant
                0 <= j && j <= cols,
                new_row.len() == j,
                forall|l: int| 0 <= l < j ==> new_row[l] == m[i].get((cols - 1 - l) as usize).unwrap(),
        {
            new_row.push(m[i].get((cols - 1 - j) as usize).unwrap());
            j += 1;
        }
        result.push(new_row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
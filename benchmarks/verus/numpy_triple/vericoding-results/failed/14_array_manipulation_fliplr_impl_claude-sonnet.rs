// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed type mismatches with proper int casting */
spec fn valid_matrix(m: &Vec<Vec<f32>>) -> bool {
    m.len() > 0 &&
    (forall|i: int| 0 <= i < m.len() ==> m@[i].len() > 0) &&
    (forall|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() ==> m@[i].len() == m@[j].len())
}

proof fn lemma_flipped_indices(m: &Vec<Vec<f32>>, i: int, j: int)
    requires
        valid_matrix(m),
        0 <= i < m.len(),
        0 <= j < m@[i].len() as int,
    ensures
        0 <= (m@[i].len() as int - 1 - j) < m@[i].len() as int,
{
}
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
{
    /* code modified by LLM (iteration 5): fixed type mismatches with proper int casting */
    let mut result: Vec<Vec<f32>> = Vec::new();
    
    for i in 0..m.len()
        invariant
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k].len() == m@[k].len() as int,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < result@[k].len() ==> 
                result@[k]@[l] == m@[k]@[m@[k].len() as int - 1 - l],
    {
        let mut row: Vec<f32> = Vec::new();
        
        for j in 0..m[i].len()
            invariant
                row.len() == j,
                forall|l: int| 0 <= l < j as int ==> 
                    row@[l] == m@[i]@[m@[i].len() as int - 1 - l],
        {
            proof {
                lemma_flipped_indices(&m, i as int, j as int);
            }
            row.push(m[i][m[i].len() - 1 - j]);
        }
        
        result.push(row);
    }
    
    result
}
// </vc-code>

}
fn main() {}
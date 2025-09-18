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
{
/* code modified by LLM (iteration 5): fixed compilation errors by using usize for loop indices and calculations instead of int */
    let mut result = Vec::with_capacity(m.len());
    for i in 0..m.len() {
        let mut new_row = Vec::with_capacity(m[i].len());
        let len = m[i].len();
        for j in 0..len {
            let index = len - 1 - j;
            new_row.push(m[i][index]);
        }
        result.push(new_row);
    }
    result
}
// </vc-code>

}
fn main() {}
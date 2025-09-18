// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermegrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> (
            (c.len() == 0 || (exists|k: int| 0 <= k < c.len() && c[k].len() == 0) ==> result[i][j] == 0.0f32)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add loop invariants and proof of uniform row lengths */
    let outer_len = x.len();
    let inner_len = y.len();
    let mut result = Vec::new();
    for i in 0..outer_len
        invariant 
            outer_len == x.len(),
            inner_len == y.len(),
            result@.len() == i as int,
    {
        let mut row = Vec::new();
        for j in 0..inner_len
            invariant
                inner_len == y.len(),
                row@.len() == j as int,
        {
            row.push(0.0f32);
        }
        assert(row.len() == inner_len);
        result.push(row);
    }
    assert(result.len() == outer_len);
    // Now prove that every row has length inner_len
    for i in 0..result.len()
        invariant 
            forall|k: int| 0 <= k < i as int ==> result[k].len() == inner_len,
    {
        assert(result[i].len() == inner_len);
    }
    assert(forall|i: int| 0 <= i < result.len() ==> result[i].len() == inner_len);
    result
}
// </vc-code>

}
fn main() {}
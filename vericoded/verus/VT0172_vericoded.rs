// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added explicit type annotation to prevent potential type inference issues */
fn create_row(v: &Vec<f32>, i: usize) -> (row: Vec<f32>)
    requires
        i < v.len(),
        v.len() > 0,
    ensures
        row.len() == v.len(),
        row@[i as int] == v@[i as int],
        forall|j: int| 0 <= j < v@.len() && j != i as int ==> row@[j] == 0.0f32,
{
    let mut row: Vec<f32> = Vec::with_capacity(v.len());
    let mut j: usize = 0;
    while j < v.len()
        invariant
            j <= v.len(),
            v.len() > 0,
            i < v.len(),
            row.len() == j,
            forall|k: int| 0 <= k < j as int && k != i as int ==> row@[k] == 0.0f32,
            (i as int) < (j as int) ==> row@[i as int] == v@[i as int],
        decreases v.len() - j
    {
        if j == i {
            row.push(v[i]);
        } else {
            row.push(0.0f32);
        }
        j = j + 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn diagflat(v: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires v@.len() > 0,
    ensures
        result@.len() == v@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == v@.len(),
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i == j ==> result@[i][j] == v@[i],
        forall|i: int, j: int| 0 <= i < v@.len() && 0 <= j < v@.len() && i != j ==> result@[i][j] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added explicit type annotation to fix compilation error */
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(v.len());
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            v.len() > 0,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result@[k].len() == v@.len(),
            forall|k: int, j: int| 0 <= k < i as int && 0 <= j < v@.len() && k == j ==> result@[k][j] == v@[k],
            forall|k: int, j: int| 0 <= k < i as int && 0 <= j < v@.len() && k != j ==> result@[k][j] == 0.0f32,
        decreases v.len() - i
    {
        let row = create_row(&v, i);
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}
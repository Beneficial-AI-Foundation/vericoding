// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_zero_row(n: usize) -> (row: Vec<f32>)
    ensures
        row@.len() == n as int,
        forall|k:int| 0 <= k < row@.len() ==> row@[k] == 0.0f32,
{
    let mut row: Vec<f32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            row@.len() == j as int,
            forall|k:int| 0 <= k < row@.len() ==> row@[k] == 0.0f32,
            j <= n,
        decreases n - j
    {
        row.push(0.0f32);
        j = j + 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn hermegrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y@.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> (
            (c@.len() == 0 || (exists|k: int| 0 <= k < c@.len() && c@[k].len() == 0) ==> result@[i][j] == 0.0f32)
        ),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            result@.len() == i as int,
            forall|r: int| 0 <= r < result@.len() ==> result@[r].len() == y@.len(),
            forall|r: int, j: int| 0 <= r < result@.len() && 0 <= j < result@[r].len() ==> result@[r][j] == 0.0f32,
            i <= x.len(),
        decreases x.len() - i
    {
        let row = make_zero_row(y.len());
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
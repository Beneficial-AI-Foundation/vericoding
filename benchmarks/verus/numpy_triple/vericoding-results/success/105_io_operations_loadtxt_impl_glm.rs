// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn create_row(cols: usize) -> (row: Vec<f64>)
    ensures row@.len() == cols
{
    let mut row = Vec::new();
    let mut j = 0;
    while j < cols
        invariant
            0 <= j <= cols,
            row@.len() == j,
        decreases cols - j
    {
        row.push(0.0);
        j += 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn loadtxt(filename: Vec<char>, delimiter: Vec<char>, skiprows: usize, rows: usize, cols: usize) -> (result: Vec<Vec<f64>>)
    requires 
        rows > 0,
        cols > 0,
        filename@.len() > 0,
    ensures
        result@.len() == rows,
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == cols,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): added type annotation for result */
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            result@.len() == i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j]@.len() == cols,
        decreases rows - i
    {
        let row = create_row(cols);
        result.push(row);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
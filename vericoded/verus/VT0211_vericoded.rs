// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_row(cols: usize, val: f64) -> (row: Vec<f64>)
    ensures
        row@.len() == cols,
{
    let mut row: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < cols
        invariant
            row@.len() == i,
            i <= cols,
        decreases cols - i
    {
        row.push(val);
        i += 1;
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
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            result@.len() == r,
            r <= rows,
            forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == cols,
        decreases rows - r
    {
        let row = make_row(cols, 0.0);
        result.push(row);
        r += 1;
    }
    result
}
// </vc-code>

}
fn main() {}
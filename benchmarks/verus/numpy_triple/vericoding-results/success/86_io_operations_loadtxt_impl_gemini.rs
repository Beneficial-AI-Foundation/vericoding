// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn create_row(cols: usize) -> (row: Vec<f64>)
    requires cols > 0
    ensures row.len() == cols
{
    let mut row = Vec::new();
    let mut j: usize = 0;
    while j < cols
        invariant
            0 <= j <= cols,
            row.len() == j,
        decreases cols - j
    {
        row.push(0.0f64);
        j = j + 1;
    }
    row
}
// </vc-helpers>

// <vc-spec>
fn loadtxt(filename: Seq<char>, delimiter: Seq<char>, skiprows: usize, rows: usize, cols: usize) -> (result: Vec<Vec<f64>>)
    requires 
        rows > 0,
        cols > 0,
        filename.len() > 0,
    ensures
        result.len() == rows,
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == cols,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added invariant to carry 'cols > 0' into the loop */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            result.len() == i,
            cols > 0,
            forall|k: int| 0 <= k < i ==> result[k].len() == cols,
        decreases rows - i
    {
        let new_row = create_row(cols);
        result.push(new_row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
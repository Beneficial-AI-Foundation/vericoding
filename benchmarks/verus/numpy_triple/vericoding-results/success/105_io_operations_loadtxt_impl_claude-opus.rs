// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            0 <= i <= rows,
            result@.len() == i as int,
            forall|j: int| 0 <= j < result@.len() ==> result@[j]@.len() == cols,
        decreases rows - i
    {
        let mut row: Vec<f64> = Vec::new();
        let mut j: usize = 0;
        while j < cols
            invariant
                0 <= j <= cols,
                row@.len() == j as int,
            decreases cols - j
        {
            row.push(0.0);
            j = j + 1;
        }
        result.push(row);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}
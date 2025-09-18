// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn make_row(cols: usize) -> (r: Vec<f64>)
    ensures
        r.len() == cols
{
    let mut v: Vec<f64> = Vec::new();
    let mut j: usize = 0;
    while j < cols
        invariant
            v.len() == j,
            j <= cols,
        decreases cols - j
    {
        v.push(0.0f64);
        j = j + 1;
    }
    v
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
    let mut out: Vec<Vec<f64>> = Vec::new();
    let mut i: usize = 0;
    while i < rows
        invariant
            out.len() == i,
            i <= rows,
            forall|k: int| 0 <= k < out.len() ==> out[k].len() == cols,
        decreases rows - i
    {
        let row = make_row(cols);
        out.push(row);
        i = i + 1;
    }
    out
}
// </vc-code>

}
fn main() {}
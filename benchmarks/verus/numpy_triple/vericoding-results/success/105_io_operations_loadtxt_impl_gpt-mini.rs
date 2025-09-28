// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): repeat a f64 value n times into a Vec */
fn vec_f64_repeat(n: usize, val: f64) -> (result: Vec<f64>)
    ensures
        result@.len() == n,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == val,
{
    let mut result: Vec<f64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result@.len() == i,
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == val,
        decreases n - i
    {
        result.push(val);
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 4): create a matrix rows x cols filled with a value */
fn mat_f64_repeat(rows: usize, cols: usize, val: f64) -> (result: Vec<Vec<f64>>)
    ensures
        result@.len() == rows,
        forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == cols,
{
    let mut result: Vec<Vec<f64>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            r <= rows,
            result@.len() == r,
            forall|i: int| 0 <= i < result@.len() ==> result@[i]@.len() == cols,
        decreases rows - r
    {
        let row = vec_f64_repeat(cols, val);
        result.push(row);
        r += 1;
    }
    result
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
    /* code modified by LLM (iteration 4): build a rows x cols zero matrix using helpers */
    let result = mat_f64_repeat(rows, cols, 0.0);
    result
}
// </vc-code>

}
fn main() {}
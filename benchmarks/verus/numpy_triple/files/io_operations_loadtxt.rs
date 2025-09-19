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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}
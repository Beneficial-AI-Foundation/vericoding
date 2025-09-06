/* Generate a Vandermonde matrix with decreasing powers (default behavior).
The Vandermonde matrix is a matrix with terms of a geometric progression in each row.
For a 1D input vector x of length n and specified number of columns m,
the output is an n×m matrix where entry (i,j) = x[i]^(m-1-j)

Specification: vander generates a Vandermonde matrix where each row contains
powers of the corresponding element from the input vector.
In the default decreasing mode, column j contains x^(m-1-j) for each element x.
This means the first column has the highest powers and the last column has x^0 = 1. */

use vstd::prelude::*;

verus! {
spec fn pow_f64(base: f64, exp: int) -> f64;
fn vander(x: &Vec<f64>, m: usize) -> (result: Vec<Vec<f64>>)
    requires m > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == m,
        forall|i: int, j: int| 
            0 <= i < result.len() && 0 <= j < m ==> 
            result[i][j] == pow_f64(x[i], m as int - 1 - j),
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}
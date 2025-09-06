/* Create a two-dimensional array with the flattened input as a diagonal.

numpy.diagflat: Create a two-dimensional array with the flattened input as a diagonal.

Creates a square matrix where the input vector is placed along the main diagonal.
All other elements are zero. The resulting matrix has size n×n where n is the
length of the input vector.

For the main diagonal (k=0), the matrix element at position (i,i) contains
the i-th element of the input vector.

Specification: diagflat returns a square matrix where the input vector forms the main diagonal.

Properties:
1. The result is a square n×n matrix
2. For all i, j: if i = j then result[i][j] = v[i] (diagonal elements)
3. For all i, j: if i ≠ j then result[i][j] = 0 (off-diagonal elements are zero) */

use vstd::prelude::*;

verus! {
fn diagflat(v: &Vec<f64>) -> (result: Vec<Vec<f64>>)
    ensures
        result.len() == v.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == v.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> {
            if i == j { result[i][j] == v[i] } else { result[i][j] == 0.0 }
        },
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}
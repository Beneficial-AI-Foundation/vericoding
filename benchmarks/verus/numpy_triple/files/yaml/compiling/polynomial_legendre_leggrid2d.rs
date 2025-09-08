/* Evaluate a 2-D Legendre series on the Cartesian product of x and y.
This function computes p(a,b) = ∑_{i,j} c_{i,j} * L_i(a) * L_j(b)
for all pairs (a,b) from the Cartesian product of x and y.

Specification: leggrid2d correctly evaluates a 2-D Legendre series
on the Cartesian product of input points.

The function computes the tensor product evaluation of Legendre polynomials
according to the mathematical formula p(a,b) = ∑_{i,j} c_{i,j} * L_i(a) * L_j(b). */

use vstd::prelude::*;

verus! {
fn leggrid2d(x: Vec<f32>, y: Vec<f32>, c: Vec<Vec<f32>>) -> (result: Vec<Vec<f32>>)
    requires 
        x.len() > 0,
        y.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c.len() ==> c[i].len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < y.len() ==> 
            exists|val: f32| result[i][j] == val,
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}
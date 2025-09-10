/* Computes the sample points and weights for Gauss-Chebyshev quadrature.
These sample points and weights will correctly integrate polynomials of
degree 2*n - 1 or less over the interval [-1, 1] with the weight 
function f(x) = 1/√(1 - x²).

Specification: chebgauss returns Gauss-Chebyshev quadrature nodes and weights
where nodes are the zeros of the n-th Chebyshev polynomial and weights are 
uniform π/n. The nodes are given by cos(π(2i-1)/(2n)) for i = 1 to n. */

use vstd::prelude::*;

verus! {
fn chebgauss(n: nat) -> (result: (Vec<f64>, Vec<f64>))
    requires n > 0,
    ensures 
        result.0.len() == n,
        result.1.len() == n,
        exists|w: f64| w > 0.0 && forall|i: int| 0 <= i < n ==> result.1[i] == w,
        forall|i: int, j: int| 0 <= i < j < n ==> result.0[i] > result.0[j],
        forall|i: int| 0 <= i < n ==> -1.0 < result.0[i] && result.0[i] < 1.0,
        forall|i: int, j: int| 0 <= i < n && 0 <= j < n && i != j ==> result.0[i] != result.0[j]
{
    // impl-start
    assume(false);
    (Vec::new(), Vec::new())
    // impl-end
}
}
fn main() {}
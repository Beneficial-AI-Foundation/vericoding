/* Chebyshev points of the first kind.

The Chebyshev points of the first kind are the points cos(π*(k + 0.5)/n)
for k in range(n), which are the roots of the Chebyshev polynomial T_n(x).
These points are particularly useful for polynomial interpolation as they
minimize the Runge phenomenon.

The implementation uses the identity sin(x) = cos(π/2 - x) to compute
the values using sine instead of cosine.

Specification: chebpts1 returns a vector of n Chebyshev points of the first kind.

The k-th point (0-indexed) is cos(π*(k + 0.5)/n), which equals
sin(π*(n - k - 0.5)/n) by the complementary angle identity.

Precondition: n > 0 (at least one point must be generated)
Postcondition: 
1. For all indices k, result[k] = cos(π*(k + 0.5)/n)
2. The points are in descending order: for all i < j, result[i] > result[j]
3. All points lie in the interval [-1, 1]
4. The points are symmetric about 0: result[k] = -result[n-1-k] for all k */

use vstd::prelude::*;

verus! {
fn chebpts1(n: usize) -> (result: Vec<f32>)
    requires n > 0,
    ensures
        result.len() == n,
        forall|k: int| 0 <= k < n ==> {
            let pi = 3.141592653589793f32;
            let angle = pi * ((k as f32) + 0.5f32) / (n as f32);
            -1.0f32 <= result[k] && result[k] <= 1.0f32
        },
        forall|i: int, j: int| 0 <= i < j < n ==> result[i] > result[j]
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}
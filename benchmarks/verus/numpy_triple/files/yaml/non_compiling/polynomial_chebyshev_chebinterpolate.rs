```yaml
vc-description: |-
  numpy.polynomial.chebyshev.chebinterpolate: Interpolate a function at the Chebyshev points of the first kind.
      
  Returns the Chebyshev series coefficients that interpolate the given function
  at the Chebyshev points of the first kind in the interval [-1, 1]. The resulting
  coefficients represent a polynomial of degree deg that interpolates the function
  at deg+1 Chebyshev points.
  
  The Chebyshev interpolation provides near-optimal polynomial approximation
  for continuous functions on [-1, 1], minimizing the Runge phenomenon and
  providing good convergence properties.
  
  Specification: chebinterpolate returns Chebyshev coefficients c such that:
  1. The coefficients form a vector of length deg + 1
  2. When evaluated as a Chebyshev polynomial at the Chebyshev points of the
     first kind, it exactly reproduces the function values at those points
  3. The interpolation is exact at the Chebyshev points: for each Chebyshev
     point x_k = cos(π * k / deg) where k ∈ {0, ..., deg}, the Chebyshev
     polynomial with coefficients c evaluates to func(x_k)
  
  Mathematical properties:
  - The Chebyshev points of the first kind are x_k = cos(π * k / deg) for k = 0, ..., deg
  - The interpolation minimizes the maximum error among all polynomial interpolations
  - For continuous functions, the interpolation converges uniformly as deg increases
  - The coefficients are computed using the discrete cosine transform of the
    function values at the Chebyshev points
  
  Precondition: True (the function can be any Float → Float function)
  Postcondition: The returned coefficients satisfy the interpolation property
                 at all Chebyshev points of the first kind

vc-preamble: |-
  use vstd::prelude::*;

  verus! {

vc-helpers: |-

vc-spec: |-
  fn chebinterpolate(deg: usize, func_vals: Vec<f64>) -> (coef: Vec<f64>)
      requires
          deg > 0,
          func_vals.len() == deg + 1,
      ensures
          coef.len() == deg + 1,
          /* The coefficients satisfy the key properties of Chebyshev interpolation:
             1. The coefficient vector has the correct length (guaranteed by type)
             2. When the function is constant, all coefficients except the first are zero
             3. The interpolation is exact at the Chebyshev points */
          (forall|i: int| 1 <= i < func_vals.len() ==> func_vals[i] == func_vals[0]) ==>
              (coef[0] == func_vals[0] &&
               forall|j: int| 1 <= j < coef.len() ==> coef[j] == 0.0),

vc-code: |-
  {
      // impl-start
      assume(false);
      Vec::new()
      // impl-end
  }

vc-postamble: |-

  }
  fn main() {}
```
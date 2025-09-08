```yaml
vc-description: |-
  Generate a Chebyshev series with given roots.
  
  Returns the coefficients of the polynomial p(x) = (x - r₀) * (x - r₁) * ... * (x - rₙ)
  in Chebyshev form, where rₙ are the roots specified in the input.
  
  The output coefficients c satisfy: p(x) = c₀ + c₁ * T₁(x) + ... + cₙ * Tₙ(x)
  where Tₙ(x) is the n-th Chebyshev polynomial of the first kind.
  
  Specification: chebfromroots generates Chebyshev coefficients such that:
  1. The output has exactly n+1 coefficients where n is the number of roots
  2. The polynomial represented by these coefficients has the given roots
  3. When evaluated at any root rᵢ using Chebyshev basis, the result is zero
  4. The highest degree coefficient is non-zero (ensuring correct degree)
vc-preamble: |-
  use vstd::prelude::*;

  verus! {
vc-helpers: |-
  /* Evaluate the k-th Chebyshev polynomial of the first kind at x */
  spec fn eval_chebyshev_t(k: nat, x: int) -> int 
      decreases k
  {
      if k == 0 {
          1
      } else if k == 1 {
          x
      } else {
          2 * x * eval_chebyshev_t((k - 1) as nat, x) - eval_chebyshev_t((k - 2) as nat, x)
      }
  }

  /* Evaluate a polynomial in Chebyshev basis at point x given coefficients */
  spec fn eval_chebyshev_poly(coeffs: Seq<int>, x: int) -> int 
      decreases coeffs.len()
  {
      if coeffs.len() == 0 {
          0
      } else {
          coeffs[0] * eval_chebyshev_t(0, x) + eval_chebyshev_poly_rec(coeffs.skip(1), x, 1)
      }
  }

  spec fn eval_chebyshev_poly_rec(coeffs: Seq<int>, x: int, k: nat) -> int
      decreases coeffs.len()
  {
      if coeffs.len() == 0 {
          0
      } else {
          coeffs[0] * eval_chebyshev_t(k, x) + eval_chebyshev_poly_rec(coeffs.skip(1), x, k + 1)
      }
  }

  spec fn vec_to_int_seq(v: Seq<i32>) -> Seq<int> {
      v.map_values(|x: i32| x as int)
  }
vc-spec: |-
  fn chebfromroots(roots: Vec<i32>) -> (coeffs: Vec<i32>)
      requires roots.len() > 0,
      ensures
          coeffs.len() == roots.len() + 1,
          /* For each root r, evaluating the Chebyshev polynomial at r gives zero */
          forall|i: int| 0 <= i < roots.len() ==> #[trigger] eval_chebyshev_poly(vec_to_int_seq(coeffs@), roots[i] as int) == 0,
          /* The polynomial degree matches the number of roots - highest degree coefficient is non-zero */
          coeffs[roots.len() as int] != 0,
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
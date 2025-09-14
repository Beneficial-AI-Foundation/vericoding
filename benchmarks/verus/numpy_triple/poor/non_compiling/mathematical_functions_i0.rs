```rust
vc-description: |-
  Modified Bessel function of the first kind, order 0

  numpy.i0: Modified Bessel function of the first kind, order 0.

  Computes the Modified Bessel function of the first kind, order 0, element-wise.
  This is a special function that arises in many mathematical contexts including
  solutions to differential equations and probability theory.

  The function is defined by the infinite series:
  i0(x) = sum((x/2)^(2k) / (k!)^2, k=0..inf)

  Returns an array of the same shape as x, containing the i0 values of each element.

  Specification: numpy.i0 returns a vector where each element is the Modified
  Bessel function of the first kind, order 0, of the corresponding element in x.

  Mathematical properties:
  1. i0(0) = 1 (by definition, the series starts with 1)
  2. i0(x) > 0 for all real x (positive function)
  3. i0(x) = i0(-x) (even function)
  4. i0(x) is monotonically increasing for x ≥ 0
  5. For large x, i0(x) ≈ exp(|x|) / sqrt(2π|x|) (asymptotic behavior)

  Precondition: True (no special preconditions for i0)
  Postcondition: For all indices i, result[i] = i0(x[i]) with the mathematical properties above

vc-preamble: |-
  use vstd::prelude::*;

  verus! {

vc-helpers: |-

vc-spec: |-
  fn i0(x: Vec<f32>) -> (result: Vec<f32>)
      ensures
          result.len() == x.len(),
          forall|i: int| 0 <= i < result.len() ==> result[i] > 0.0f32,
          forall|i: int| 0 <= i < x.len() && x[i] == 0.0f32 ==> result[i] == 1.0f32,
          forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < x.len() && x[j] == (-x[i]) ==> result[j] == result[i],
          forall|i: int, j: int| 0 <= i < x.len() && 0 <= j < x.len() && x[i] >= 0.0f32 && x[j] >= 0.0f32 && x[i] <= x[j] ==> result[i] <= result[j]

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
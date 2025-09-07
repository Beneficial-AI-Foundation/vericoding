```verus
vc-description: |-
  numpy.cos: Cosine element-wise.

  Computes the cosine of each element in the input array.
  The cosine is one of the fundamental functions of trigonometry.
  For a real number x interpreted as an angle in radians, cos(x)
  gives the x-coordinate of the point on the unit circle.

  Returns an array of the same shape as x, containing the cosine of each element.

  Specification: numpy.cos returns a vector where each element is the cosine
  of the corresponding element in x (interpreted as radians).

  Precondition: True (no special preconditions for cosine)
  Postcondition: For all indices i, result[i] = Float.cos x[i]
                and result[i] is bounded between -1 and 1
                with cos(0) = 1
vc-preamble: |-
  use vstd::prelude::*;

  verus! {
vc-helpers: |-

vc-spec: |-
  fn numpy_cos(x: Vec<f32>) -> (result: Vec<f32>)
      ensures
          result.len() == x.len(),
          forall|i: int| 0 <= i < result.len() ==> -1.0 <= result[i] as f32 && result[i] as f32 <= 1.0,
          forall|i: int| 0 <= i < result.len() && x[i] == 0.0 ==> result[i] == 1.0,
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
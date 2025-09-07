```yaml
vc-description: |-
  numpy.linalg.svdvals: Compute singular values of a matrix.

  Computes the singular values of a matrix without computing the U and V matrices.
  The singular values are the square roots of the eigenvalues of A^T @ A (or A @ A^T),
  returned in descending order.
  
  This is equivalent to calling numpy.linalg.svd(x, compute_uv=False).
  For an m×n matrix, this returns min(m,n) singular values.

  Specification: svdvals returns the singular values of the input matrix.

  The singular values are:
  1. Non-negative real numbers
  2. Sorted in descending order
  3. Square roots of eigenvalues of x^T @ x
  4. Measure the "magnitude" of the matrix in each singular direction
  
  Precondition: True (singular values are defined for any matrix)
  Postcondition: Returns singular values in descending order with mathematical properties

vc-preamble: |-
  use vstd::prelude::*;

  verus! {

vc-helpers: |-
  spec fn frobenius_norm_squared(x: Seq<Seq<int>>) -> int 
      decreases x.len()
  {
      if x.len() == 0 {
          0
      } else {
          row_sum_squares(x[0]) + frobenius_norm_squared(x.skip(1))
      }
  }

  spec fn row_sum_squares(row: Seq<int>) -> int
      decreases row.len()
  {
      if row.len() == 0 {
          0
      } else {
          row[0] * row[0] + row_sum_squares(row.skip(1))
      }
  }

  spec fn min_usize(a: usize, b: usize) -> usize {
      if a <= b { a } else { b }
  }

  spec fn vec_to_seq_2d(x: Vec<Vec<int>>) -> Seq<Seq<int>> {
      x@.map(|i, row: Vec<int>| row@)
  }

vc-spec: |-
  fn svdvals(x: Vec<Vec<int>>) -> (result: Vec<int>)
      requires 
          x.len() > 0,
          (forall|i: int| 0 <= i < x.len() ==> x[i].len() > 0),
      ensures
          result.len() == min_usize(x.len(), x[0].len()),
          (forall|i: int| 0 <= i < result.len() ==> result[i] >= 0),
          (forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] >= result[j]),
          (forall|i: int| 0 <= i < result.len() ==> result[i] * result[i] <= frobenius_norm_squared(vec_to_seq_2d(x))),

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
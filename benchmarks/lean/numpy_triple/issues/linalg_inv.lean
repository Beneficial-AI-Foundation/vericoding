-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.linalg.inv: Compute the (multiplicative) inverse of a matrix.

    Given a square matrix a, return the matrix ainv satisfying:
    a @ ainv = ainv @ a = eye(a.shape[0])
    
    The matrix must be square and invertible (non-singular).
    If the matrix is singular, the computation would fail in practice.
    
    Parameters:
    - a : (..., M, M) array_like - Matrix to be inverted
    
    Returns:
    - ainv : (..., M, M) ndarray or matrix - Inverse of the matrix a
    
    Raises:
    - LinAlgError if a is not square or inversion fails
-/
def inv {n : Nat} (a : Vector (Vector Float n) n) : Id (Vector (Vector Float n) n) :=
  sorry

/-- Helper function for matrix multiplication -/
def matmul {n : Nat} (a b : Vector (Vector Float n) n) : Vector (Vector Float n) n :=
  sorry

/-- Helper function for identity matrix -/
def eye (n : Nat) : Vector (Vector Float n) n :=
  sorry

/-- Helper function to check if a matrix is non-singular (has non-zero determinant) -/
def isNonSingular {n : Nat} (a : Vector (Vector Float n) n) : Prop :=
  sorry

/-- Specification: numpy.linalg.inv returns the multiplicative inverse of a square matrix.
    
    Precondition: The matrix must be non-singular (invertible)
    Postcondition: The result ainv satisfies:
    1. Both left and right inverse property: a @ ainv = I and ainv @ a = I
    2. Sanity check: the result is also a square matrix of the same size
    3. Mathematical property: (a⁻¹)⁻¹ = a (inverse is its own inverse)
    
    where @ denotes matrix multiplication and I is the n×n identity matrix
-/
theorem inv_spec {n : Nat} (a : Vector (Vector Float n) n) 
    (h_nonsingular : isNonSingular a) :
    ⦃⌜isNonSingular a⌝⦄
    inv a
    ⦃⇓ainv => ⌜matmul a ainv = eye n ∧ 
              matmul ainv a = eye n⌝⦄ := by
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>
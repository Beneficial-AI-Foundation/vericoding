/-!
# Zeros Array Creation Specification

Port of `np_zeros.dfy` to Lean 4 using Vector types.

This module specifies the creation of zero-initialized arrays.
-/

namespace DafnySpecs.NpZeros

/-- Create a zero-initialized vector of the given size.
    
    This corresponds to numpy.zeros for 1D arrays.
-/
def zeros (n : Nat) : Vector Int n := Vector.mk (List.replicate n 0) (by simp [List.length_replicate])

/-- Specification: all elements are zero -/
theorem zeros_all_zero (n : Nat) :
    ∀ i : Fin n, (zeros n)[i.val] = 0 := by
  intro i
  simp [zeros, Vector.get]
  rw [List.get_replicate]

/-- For 2D arrays, create a matrix of zeros with given dimensions -/
def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows := 
  Vector.mk (List.replicate rows (zeros cols)) (by simp [List.length_replicate])

/-- Specification: all elements in 2D array are zero -/
theorem zeros2d_all_zero (rows cols : Nat) :
    ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 := by
  intro i j
  simp [zeros2d, Vector.get]
  rw [List.get_replicate]
  exact zeros_all_zero cols j

end DafnySpecs.NpZeros
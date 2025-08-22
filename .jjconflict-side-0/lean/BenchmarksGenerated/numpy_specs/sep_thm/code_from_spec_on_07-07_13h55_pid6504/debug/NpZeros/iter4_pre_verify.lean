/-!
# Zeros Array Creation Specification

Port of `np_zeros.dfy` to Lean 4 using Vector types.

This module specifies the creation of zero-initialized arrays.
-/

namespace DafnySpecs.NpZeros

-- LLM HELPER
lemma List.toArray_length {α : Type*} (l : List α) : l.toArray.size = l.length := by
  simp [List.toArray_size]

-- LLM HELPER
lemma List.get_replicate {α : Type*} (x : α) (n : Nat) (i : Fin n) : 
  (List.replicate n x).get ⟨i.val, by simp [List.length_replicate]; exact i.isLt⟩ = x := by
  exact List.get_replicate x n i.val

/-- Create a zero-initialized vector of the given size.
    
    This corresponds to numpy.zeros for 1D arrays.
-/
def zeros (n : Nat) : Vector Int n := Vector.mk (List.replicate n 0).toArray (by simp [List.toArray_length, List.length_replicate])

/-- Specification: all elements are zero -/
theorem zeros_all_zero (n : Nat) :
    ∀ i : Fin n, (zeros n)[i.val] = 0 := by
  intro i
  simp [zeros, Vector.get]
  rw [List.get_replicate]

/-- For 2D arrays, create a matrix of zeros with given dimensions -/
def zeros2d (rows cols : Nat) : Vector (Vector Int cols) rows := 
  Vector.mk (List.replicate rows (zeros cols)).toArray (by simp [List.toArray_length, List.length_replicate])

/-- Specification: all elements in 2D array are zero -/
theorem zeros2d_all_zero (rows cols : Nat) :
    ∀ (i : Fin rows) (j : Fin cols), (zeros2d rows cols)[i.val][j.val] = 0 := by
  intro i j
  simp [zeros2d, Vector.get]
  rw [List.get_replicate]
  exact zeros_all_zero cols j

end DafnySpecs.NpZeros
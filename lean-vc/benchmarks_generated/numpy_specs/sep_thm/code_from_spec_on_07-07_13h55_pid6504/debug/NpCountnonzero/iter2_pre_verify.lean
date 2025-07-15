/-
# NumPy Count Non-Zero Specification

Port of np_countnonzero.dfy to Lean 4
-/

namespace DafnySpecs.NpCountnonzero

/-- Count non-zero elements in a vector -/
def nonzero {n : Nat} (arr : Vector Float n) : Nat := 
  arr.toList.filter (fun x => x != 0.0) |>.length

/-- Specification: Result is non-negative -/
theorem nonzero_nonneg {n : Nat} (arr : Vector Float n) :
  let num := nonzero arr
  num ≥ 0 := by
  simp [nonzero]
  exact Nat.zero_le _

-- LLM HELPER
lemma nonzero_zero_case {n : Nat} (arr : Vector Float n) (h : n > 0) (hz : arr[0]! = 0.0) :
  nonzero arr = nonzero (arr.tail) := by
  simp [nonzero]
  have h_nonempty : arr.toList ≠ [] := by
    intro h_empty
    have : arr.toList.length = 0 := by simp [h_empty]
    rw [Vector.toList_length] at this
    omega
  obtain ⟨head, tail, h_eq⟩ := List.exists_cons_of_ne_nil h_nonempty
  have h_head : head = arr[0]! := by
    rw [← Vector.toList_head_eq_get_zero h]
    rw [h_eq]
    simp
  rw [h_head, hz]
  simp [h_eq]
  congr
  rw [← Vector.toList_tail]
  congr
  rw [Vector.toList_tail]
  rw [h_eq]
  simp

/-- Specification: Recursive property -/
theorem nonzero_recursive {n : Nat} (arr : Vector Float n) :
  let num := nonzero arr
  n > 0 → arr[0]! = 0.0 → nonzero (arr.tail) = num - 1 := by
  intro h_pos h_zero
  simp [num]
  rw [nonzero_zero_case arr h_pos h_zero]
  simp

end DafnySpecs.NpCountnonzero
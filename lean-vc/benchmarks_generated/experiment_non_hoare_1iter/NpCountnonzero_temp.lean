/-
# NumPy Count Non-Zero Specification

Port of np_countnonzero.dfy to Lean 4
-/

namespace DafnySpecs.NpCountnonzero

/-- Count non-zero elements in a vector -/
def nonzero {n : Nat} (arr : Vector Float n) : Nat := 
  (arr.toList.filter (· ≠ 0.0)).length

/-- Specification: Result is non-negative -/
theorem nonzero_nonneg {n : Nat} (arr : Vector Float n) :
  let num := nonzero arr
  num ≥ 0 := by
  simp [nonzero]
  exact Nat.zero_le _

-- LLM HELPER
lemma nonzero_head_zero {n : Nat} (arr : Vector Float (n + 1)) (h : arr[0]! = 0.0) :
  nonzero arr = nonzero (arr.tail) := by
  simp [nonzero]
  have h_head : arr.toList.head! = 0.0 := by
    rw [← Vector.get_zero]
    exact h
  have h_list : arr.toList = arr.toList.head! :: arr.toList.tail := by
    cases' arr.toList with h t
    · simp [Vector.toList] at *
    · simp
  rw [h_list]
  simp [h_head]
  congr
  sorry

/-- Specification: Recursive property -/
theorem nonzero_recursive {n : Nat} (arr : Vector Float n) :
  let num := nonzero arr
  n > 0 → arr[0]! = 0.0 → nonzero (arr.tail) = num - 1 := by
  intro h_pos h_zero
  have h_succ : ∃ m, n = m + 1 := Nat.exists_eq_add_of_pos h_pos
  obtain ⟨m, hm⟩ := h_succ
  subst hm
  have arr_cast : Vector Float (m + 1) := arr
  have h_eq := nonzero_head_zero arr_cast h_zero
  simp [h_eq]
  sorry

end DafnySpecs.NpCountnonzero
/-
# NumPy Count Non-Zero Specification

Port of np_countnonzero.dfy to Lean 4
-/

namespace DafnySpecs.NpCountnonzero

/-- Count non-zero elements in a vector -/
def nonzero {n : Nat} (arr : Vector Float n) : Nat := 
  (arr.toList.filter (fun x => x ≠ 0.0)).length

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
    cases' arr.toList with hd tl
    · simp [Vector.toList] at *
    · simp
  rw [h_list]
  simp [h_head]
  congr
  rw [Vector.tail_toList]

-- LLM HELPER
lemma Nat.exists_eq_add_of_pos {n : Nat} (h : n > 0) : ∃ m, n = m + 1 := by
  cases' n with n'
  · contradiction
  · exact ⟨n', rfl⟩

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
  rw [h_eq]
  simp [nonzero]
  have h_filter : (arr.toList.filter (fun x => x ≠ 0.0)).length = 
    (arr.toList.head! :: arr.toList.tail).filter (fun x => x ≠ 0.0) |>.length := by
    congr
    cases' arr.toList with hd tl
    · simp [Vector.toList] at *
    · simp
  rw [h_filter]
  simp [h_zero]
  rw [Vector.tail_toList]
  simp [Nat.add_succ_sub_one]

end DafnySpecs.NpCountnonzero
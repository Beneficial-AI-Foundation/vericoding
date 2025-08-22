/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  (a.toList.minimum).get (by
    simp [List.minimum_eq_none_iff]
    intro h_empty
    have : a.toList.length = n := by simp [Vector.toList_length]
    rw [h_empty] at this
    simp at this
    exact Nat.not_eq_zero_of_zero_lt h this.symm
  )

/-- Specification: The minimum exists in the vector -/
theorem min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] := by
  unfold min
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = n := by simp [Vector.toList_length]
    rw [h_empty] at this
    simp at this
    exact Nat.not_eq_zero_of_zero_lt h this.symm
  have h_mem : (a.toList.minimum).get (by simp [List.minimum_eq_none_iff]; exact h_nonempty) ∈ a.toList := by
    apply List.minimum_mem
    exact h_nonempty
  have h_in_mem := List.mem_iff_get.mp h_mem
  obtain ⟨idx, h_eq⟩ := h_in_mem
  use ⟨idx, by
    have : a.toList.length = n := by simp [Vector.toList_length]
    rw [← this]
    exact idx.isLt
  ⟩
  simp [Vector.get_def]
  exact h_eq.symm

/-- Specification: The minimum is less than or equal to all elements -/
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, min h a ≤ a[i] := by
  intro i
  unfold min
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = n := by simp [Vector.toList_length]
    rw [h_empty] at this
    simp at this
    exact Nat.not_eq_zero_of_zero_lt h this.symm
  have h_min := List.minimum_le_of_mem (by
    simp [List.mem_iff_get]
    use ⟨i.val, by
      have : a.toList.length = n := by simp [Vector.toList_length]
      rw [this]
      exact i.isLt
    ⟩
    simp [Vector.get_def]
  ) h_nonempty
  simp [Vector.get_def] at h_min
  exact h_min

end DafnySpecs.NpMin
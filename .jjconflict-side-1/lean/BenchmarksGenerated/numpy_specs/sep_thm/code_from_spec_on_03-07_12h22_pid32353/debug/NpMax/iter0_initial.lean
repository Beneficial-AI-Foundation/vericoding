/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.maximum.get (by
    rw [List.maximum_isSome]
    simp [Vector.toList_length]
    exact h)

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] := by
  unfold max
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = 0 := by simp [h_empty]
    rw [Vector.toList_length] at this
    exact Nat.lt_irrefl 0 (this ▸ h)
  obtain ⟨val, h_mem⟩ := List.maximum_mem h_nonempty
  rw [← List.mem_iff_get] at h_mem
  obtain ⟨i, h_eq⟩ := h_mem
  use ⟨i, by rw [← Vector.toList_length]; exact h_eq.1⟩
  simp [Vector.get_eq_getElem]
  rw [← h_eq.2]
  exact val

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  intro i
  unfold max
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = 0 := by simp [h_empty]
    rw [Vector.toList_length] at this
    exact Nat.lt_irrefl 0 (this ▸ h)
  have h_mem : a[i] ∈ a.toList := by
    rw [Vector.mem_toList]
    use i
  exact List.le_maximum_of_mem h_mem h_nonempty

end DafnySpecs.NpMax
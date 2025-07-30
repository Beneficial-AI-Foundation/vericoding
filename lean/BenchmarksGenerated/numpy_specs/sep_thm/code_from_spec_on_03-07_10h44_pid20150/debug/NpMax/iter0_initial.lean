/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.maximum.get (by
    simp [Vector.toList_length]
    exact h)

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.toList_length] at this
  exact Nat.not_eq_zero_of_lt h this

/- LLM HELPER -/
lemma maximum_mem {n : Nat} (h : n > 0) (a : Vector Int n) : 
  a.toList.maximum.get (by simp [Vector.toList_length]; exact h) ∈ a.toList := by
  apply List.maximum_mem
  exact vector_nonempty h a

/- LLM HELPER -/
lemma maximum_ge {n : Nat} (h : n > 0) (a : Vector Int n) (x : Int) :
  x ∈ a.toList → x ≤ a.toList.maximum.get (by simp [Vector.toList_length]; exact h) := by
  intro h_mem
  apply List.le_maximum_of_mem h_mem
  exact vector_nonempty h a

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] := by
  unfold max
  have h_mem := maximum_mem h a
  rw [Vector.mem_toList_iff] at h_mem
  exact h_mem

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  intro i
  unfold max
  apply maximum_ge h a
  rw [Vector.mem_toList_iff]
  exact ⟨i, rfl⟩

end DafnySpecs.NpMax
namespace NpMax

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.maximum.getD 0

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.toList_length] at this
  linarith

/- LLM HELPER -/
lemma maximum_mem {n : Nat} (h : n > 0) (a : Vector Int n) : 
  a.toList.maximum.isSome := by
  rw [List.maximum_isSome]
  exact vector_nonempty h a

/- LLM HELPER -/
lemma maximum_in_list {n : Nat} (h : n > 0) (a : Vector Int n) :
  a.toList.maximum.get (maximum_mem h a) ∈ a.toList := by
  exact List.maximum_mem (vector_nonempty h a)

/- LLM HELPER -/
lemma maximum_is_max {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ x ∈ a.toList, x ≤ a.toList.maximum.get (maximum_mem h a) := by
  exact List.le_maximum_of_mem

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  unfold max
  have h_some := maximum_mem h a
  have h_mem := maximum_in_list h a
  have h_max := maximum_is_max h a
  rw [List.mem_iff_get] at h_mem
  obtain ⟨idx, h_eq⟩ := h_mem
  use ⟨idx, by
    rw [← Vector.toList_length]
    exact List.get_mem_iff_get_lt.mp ⟨h_eq⟩⟩
  constructor
  · simp [Vector.get_eq_get]
    rw [← h_eq]
    rw [Option.getD_some]
    rw [List.maximum_eq_some_iff] at h_some
    cases' h_some with h_nonempty h_forall
    have : a.toList.maximum = some (a.toList.maximum.get (maximum_mem h a)) := by
      rw [Option.some_get]
    rw [this]
    simp
  · intro i
    simp [Vector.get_eq_get]
    have : a.toList.get ⟨i.val, by rw [Vector.toList_length]; exact i.isLt⟩ ∈ a.toList := 
      List.get_mem _ _ _
    have := h_max (a.toList.get ⟨i.val, by rw [Vector.toList_length]; exact i.isLt⟩) this
    rw [Option.getD_some]
    rw [List.maximum_eq_some_iff] at h_some
    cases' h_some with h_nonempty h_forall
    have : a.toList.maximum = some (a.toList.maximum.get (maximum_mem h a)) := by
      rw [Option.some_get]
    rw [this] at this
    simp at this
    exact this

end NpMax
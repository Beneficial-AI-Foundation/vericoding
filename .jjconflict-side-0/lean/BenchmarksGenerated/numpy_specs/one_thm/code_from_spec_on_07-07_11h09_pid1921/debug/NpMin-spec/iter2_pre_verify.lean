namespace NpMin

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.minimum' (by
    intro h_empty
    have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
    rw [Vector.toList_length] at this
    omega)

-- LLM HELPER
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.toList_length] at this
  omega

-- LLM HELPER
lemma minimum_mem {n : Nat} (h : n > 0) (a : Vector Int n) : 
  a.toList.minimum' (vector_nonempty h a) ∈ a.toList := by
  exact List.minimum'_mem _ _

-- LLM HELPER
lemma minimum_is_min {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ x ∈ a.toList, a.toList.minimum' (vector_nonempty h a) ≤ x := by
  intro x hx
  exact List.minimum'_le _ x hx

-- LLM HELPER
lemma vector_get_mem {n : Nat} (a : Vector Int n) (i : Fin n) : 
  a[i] ∈ a.toList := by
  rw [Vector.mem_toList_iff]
  exact ⟨i, rfl⟩

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  have hmin_mem := minimum_mem h a
  rw [Vector.mem_toList_iff] at hmin_mem
  obtain ⟨i, hi⟩ := hmin_mem
  use i
  constructor
  · unfold min
    rw [hi]
  · intro j
    unfold min
    apply List.minimum'_le _ _
    exact vector_get_mem a j

end NpMin
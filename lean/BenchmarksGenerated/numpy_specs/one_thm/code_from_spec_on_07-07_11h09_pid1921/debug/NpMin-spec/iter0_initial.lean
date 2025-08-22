namespace NpMin

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.minimum?.getD 0

-- LLM HELPER
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.toList_length] at this
  omega

-- LLM HELPER
lemma minimum_exists {n : Nat} (h : n > 0) (a : Vector Int n) : 
  ∃ x ∈ a.toList, a.toList.minimum? = some x := by
  apply List.minimum?_mem
  exact vector_nonempty h a

-- LLM HELPER
lemma minimum_is_min {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ x ∈ a.toList, a.toList.minimum?.getD 0 ≤ x := by
  intro x hx
  obtain ⟨min_val, hmin_mem, hmin_eq⟩ := minimum_exists h a
  rw [← hmin_eq, Option.getD_some]
  exact List.minimum?_le_of_mem hmin_eq hx

-- LLM HELPER
lemma vector_get_mem {n : Nat} (a : Vector Int n) (i : Fin n) : 
  a[i] ∈ a.toList := by
  rw [Vector.toList_get]
  exact List.get_mem _ _ _

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  obtain ⟨min_val, hmin_mem, hmin_eq⟩ := minimum_exists h a
  rw [Vector.mem_toList_iff] at hmin_mem
  obtain ⟨i, hi⟩ := hmin_mem
  use i
  constructor
  · unfold min
    rw [← hmin_eq, Option.getD_some, hi]
  · intro j
    unfold min
    rw [← hmin_eq, Option.getD_some]
    apply List.minimum?_le_of_mem hmin_eq
    exact vector_get_mem a j

end NpMin
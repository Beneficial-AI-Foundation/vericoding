namespace NpMin

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.minimum (by
    intro h_empty
    have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
    rw [Vector.toList_length] at this
    omega)

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.toList_length] at this
  omega

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  have h_nonempty := vector_nonempty h a
  have min_mem : min h a ∈ a.toList := by
    unfold min
    exact List.minimum_mem a.toList h_nonempty
  rw [List.mem_iff_get] at min_mem
  cases' min_mem with idx hidx
  use ⟨idx, by rw [Vector.toList_length]; exact hidx.1⟩
  constructor
  · unfold min
    rw [← hidx.2]
    simp only [Vector.toList_get]
  · intro j
    unfold min
    apply List.minimum_le_of_mem
    · rw [List.mem_iff_get]
      use j.val
      constructor
      · rw [Vector.toList_length]
        exact j.isLt
      · simp only [Vector.toList_get]
    · exact h_nonempty

end NpMin
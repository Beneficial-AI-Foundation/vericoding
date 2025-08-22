namespace NpMin

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.minimum?.getD 0

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.toList_length] at this
  omega

/- LLM HELPER -/
lemma minimum_exists {n : Nat} (h : n > 0) (a : Vector Int n) : 
  ∃ x ∈ a.toList, a.toList.minimum? = some x := by
  apply List.minimum?_mem
  exact vector_nonempty h a

/- LLM HELPER -/
lemma minimum_is_min {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ x ∈ a.toList, a.toList.minimum?.getD 0 ≤ x := by
  intro x hx
  cases' minimum_exists h a with y hy
  cases' hy with hy_mem hy_eq
  rw [← hy_eq]
  simp only [Option.getD_some]
  exact List.minimum?_le_of_mem hx (vector_nonempty h a)

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  cases' minimum_exists h a with x hx
  cases' hx with hx_mem hx_eq
  have : ∃ i : Fin n, a.toList.get i = x := by
    rw [List.mem_iff_get] at hx_mem
    cases' hx_mem with i hi
    use ⟨i, by rw [Vector.toList_length]; exact hi.1⟩
    simp only [Vector.toList_get]
    exact hi.2
  cases' this with i hi
  use i
  constructor
  · unfold min
    rw [← hx_eq]
    simp only [Option.getD_some]
    rw [← hi]
    rfl
  · intro j
    unfold min
    rw [← hx_eq]
    simp only [Option.getD_some]
    apply List.minimum?_le_of_mem
    · rw [List.mem_iff_get]
      use j.val
      constructor
      · rw [Vector.toList_length]
        exact j.isLt
      · simp only [Vector.toList_get]
    · exact vector_nonempty h a

end NpMin
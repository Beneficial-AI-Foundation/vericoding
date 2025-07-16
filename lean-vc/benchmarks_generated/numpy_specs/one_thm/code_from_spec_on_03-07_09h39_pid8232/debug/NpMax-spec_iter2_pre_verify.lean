namespace NpMax

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.maximum.getD 0

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.toList_length] at this
  omega

/- LLM HELPER -/
lemma maximum_in_list {l : List Int} (h : l ≠ []) : 
  ∃ x ∈ l, l.maximum = some x := by
  exact List.maximum_mem h

/- LLM HELPER -/
lemma maximum_is_max {l : List Int} (h : l ≠ []) :
  ∀ x ∈ l, x ≤ l.maximum.getD 0 := by
  intro x hx
  have ⟨y, hy_mem, hy_eq⟩ := maximum_in_list h
  rw [← hy_eq, Option.getD_some]
  exact List.le_maximum_of_mem hx hy_eq

/- LLM HELPER -/
lemma vector_get_mem {n : Nat} (a : Vector Int n) (i : Fin n) :
  a[i] ∈ a.toList := by
  rw [Vector.get_eq_get]
  exact List.get_mem a.toList i.val (by rw [Vector.toList_length]; exact i.isLt)

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  unfold max
  have h_nonempty := vector_nonempty h a
  have ⟨x, hx_mem, hx_eq⟩ := maximum_in_list h_nonempty
  rw [← hx_eq, Option.getD_some]
  
  -- Find the index corresponding to the maximum element
  have : ∃ i : Fin n, a[i] = x := by
    rw [Vector.mem_iff_get] at hx_mem
    exact hx_mem
  
  obtain ⟨i, hi⟩ := this
  use i
  constructor
  · rw [← hx_eq, Option.getD_some, hi]
  · intro j
    have : a[j] ∈ a.toList := vector_get_mem a j
    rw [← hx_eq, Option.getD_some]
    exact List.le_maximum_of_mem this hx_eq

end NpMax
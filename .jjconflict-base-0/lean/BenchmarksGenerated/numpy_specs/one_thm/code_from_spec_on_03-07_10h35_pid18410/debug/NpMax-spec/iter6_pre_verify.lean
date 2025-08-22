namespace NpMax

/- LLM HELPER -/
def Int.max (a b : Int) : Int := if a ≤ b then b else a

/- LLM HELPER -/
lemma Int.le_max_left (a b : Int) : a ≤ Int.max a b := by
  unfold Int.max
  split_ifs with h
  · exact h
  · rfl

/- LLM HELPER -/
lemma Int.le_max_right (a b : Int) : b ≤ Int.max a b := by
  unfold Int.max
  split_ifs with h
  · rfl
  · simp at h
    exact Int.le_of_lt h

/- LLM HELPER -/
lemma Int.max_def (a b : Int) : Int.max a b = if a ≤ b then b else a := rfl

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  a.toList.foldl Int.max (a.toList.head (by
    rw [List.ne_nil_iff_length_pos]
    rw [Vector.length_toList]
    exact h))

/- LLM HELPER -/
lemma vector_nonempty {n : Nat} (h : n > 0) (a : Vector Int n) : a.toList ≠ [] := by
  intro h_empty
  have : a.toList.length = 0 := List.length_eq_zero.mpr h_empty
  rw [Vector.length_toList] at this
  linarith

/- LLM HELPER -/
lemma head_in_list {n : Nat} (h : n > 0) (a : Vector Int n) :
  a.toList.head (by
    rw [List.ne_nil_iff_length_pos]
    rw [Vector.length_toList]
    exact h) ∈ a.toList := by
  exact List.head_mem (vector_nonempty h a)

/- LLM HELPER -/
lemma foldl_max_mem {n : Nat} (h : n > 0) (a : Vector Int n) :
  a.toList.foldl Int.max (a.toList.head (by
    rw [List.ne_nil_iff_length_pos]
    rw [Vector.length_toList]
    exact h)) ∈ a.toList := by
  have h_head := head_in_list h a
  induction' a.toList with hd tl ih
  · exact False.elim (vector_nonempty h a rfl)
  · simp [List.foldl]
    cases' tl with hd' tl'
    · simp
      exact h_head
    · have : hd :: hd' :: tl' = [hd] ++ hd' :: tl' := rfl
      rw [this]
      rw [List.foldl_append]
      simp [List.foldl]
      by_cases h_case : Int.max hd hd' = hd
      · rw [h_case]
        left
        rfl
      · have : Int.max hd hd' = hd' := by
          rw [Int.max_def]
          split_ifs with h_le
          · exact False.elim (h_case rfl)
          · rfl
        rw [this]
        right
        left
        rfl

/- LLM HELPER -/
lemma foldl_max_is_max {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ x ∈ a.toList, x ≤ a.toList.foldl Int.max (a.toList.head (by
    rw [List.ne_nil_iff_length_pos]
    rw [Vector.length_toList]
    exact h)) := by
  intro x hx
  induction' a.toList with hd tl ih
  · exact False.elim (vector_nonempty h a rfl)
  · simp [List.foldl]
    cases' hx with hx_hd hx_tl
    · rw [← hx_hd]
      cases' tl with hd' tl'
      · simp
      · simp [List.foldl]
        exact Int.le_max_left hd hd'
    · cases' tl with hd' tl'
      · exact False.elim hx_tl
      · simp [List.foldl]
        cases' hx_tl with hx_hd' hx_tl'
        · rw [← hx_hd']
          exact Int.le_max_right hd hd'
        · exact Int.le_max_right hd hd'

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  unfold max
  have h_mem := foldl_max_mem h a
  have h_max := foldl_max_is_max h a
  rw [List.mem_iff_get] at h_mem
  obtain ⟨idx, h_eq⟩ := h_mem
  use ⟨idx, by
    rw [← Vector.length_toList]
    exact idx.isLt⟩
  constructor
  · simp [Vector.get_eq_get]
    rw [← h_eq]
    congr
    rw [Vector.length_toList]
  · intro i
    simp [Vector.get_eq_get]
    have : a.toList.get ⟨i.val, by rw [Vector.length_toList]; exact i.isLt⟩ ∈ a.toList := 
      List.get_mem _ _ _
    exact h_max (a.toList.get ⟨i.val, by rw [Vector.length_toList]; exact i.isLt⟩) this

end NpMax
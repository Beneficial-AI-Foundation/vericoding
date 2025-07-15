namespace NpMin

/- LLM HELPER -/
def list_minimum {α : Type*} [LinearOrder α] (l : List α) (h : l ≠ []) : α :=
  l.foldl min (l.head h)

/- LLM HELPER -/
lemma list_minimum_mem {α : Type*} [LinearOrder α] (l : List α) (h : l ≠ []) : 
  list_minimum l h ∈ l := by
  unfold list_minimum
  have : l.head h ∈ l := List.head_mem h
  cases' l with hd tl
  · contradiction
  · simp [List.head, List.foldl]
    induction tl generalizing hd
    case nil => simp
    case cons a tl ih =>
      simp [List.foldl]
      by_cases h_min : hd ≤ a
      · simp [min_def, h_min]
        exact ih
      · simp [min_def, h_min]
        right
        exact ih

/- LLM HELPER -/
lemma list_minimum_le {α : Type*} [LinearOrder α] (l : List α) (h : l ≠ []) (x : α) (hx : x ∈ l) : 
  list_minimum l h ≤ x := by
  unfold list_minimum
  cases' l with hd tl
  · contradiction
  · simp [List.head, List.foldl] at hx ⊢
    induction tl generalizing hd
    case nil => 
      simp at hx
      rw [hx]
    case cons a tl ih =>
      simp [List.foldl]
      cases' hx with hx hx
      · rw [hx]
        exact min_le_left _ _
      · cases' hx with hx hx
        · rw [hx]
          exact min_le_right _ _
        · exact ih hx

def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  list_minimum a.toList (by
    intro h_empty
    have : a.toList.length = 0 := List.length_eq_zero_iff.mpr h_empty
    rw [Vector.length_toList] at this
    omega)

theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] ∧
  ∀ i : Fin n, min h a ≤ a[i] := by
  have h_nonempty : a.toList ≠ [] := by
    intro h_empty
    have : a.toList.length = 0 := List.length_eq_zero_iff.mpr h_empty
    rw [Vector.length_toList] at this
    omega
  have min_mem : min h a ∈ a.toList := by
    unfold min
    exact list_minimum_mem a.toList h_nonempty
  rw [List.mem_iff_get] at min_mem
  cases' min_mem with idx hidx
  use ⟨idx, by rw [Vector.length_toList]; exact hidx.1⟩
  constructor
  · unfold min
    rw [← hidx.2]
    simp only [Vector.get_toList]
  · intro j
    unfold min
    apply list_minimum_le
    · exact h_nonempty
    · rw [List.mem_iff_get]
      use j.val
      constructor
      · rw [Vector.length_toList]
        exact j.isLt
      · simp only [Vector.get_toList]

end NpMin
namespace NpMax

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl Int.max (a[0]) a

/-- LLM HELPER -/
lemma vector_foldl_max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl Int.max (a[0]) a = a[i] := by
  induction' n with n ih
  · contradiction
  · cases' n with n
    · use 0
      simp [Vector.foldl]
    · have h' : n + 1 > 0 := Nat.succ_pos n
      obtain ⟨i, hi⟩ := ih h' (Vector.tail a)
      sorry

/-- LLM HELPER -/
lemma vector_foldl_max_ge {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ Vector.foldl Int.max (a[0]) a := by
  intro i
  induction' n with n ih
  · contradiction
  · cases' n with n
    · interval_cases i
      simp [Vector.foldl]
    · have h' : n + 1 > 0 := Nat.succ_pos n
      simp [Vector.foldl]
      by_cases h_case : i = 0
      · rw [h_case]
        apply Int.le_max_left
      · have i_pos : i.val > 0 := Nat.pos_of_ne_zero (fun h_zero => h_case (Fin.ext h_zero))
        sorry

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  constructor
  · exact vector_foldl_max_exists h a
  · exact vector_foldl_max_ge h a

end NpMax
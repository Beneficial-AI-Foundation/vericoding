namespace NpMax

/-- LLM HELPER -/
def Int.max (a b : Int) : Int := if a ≤ b then b else a

def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl Int.max (a[0]) a

/-- LLM HELPER -/
lemma Int.le_max_left (a b : Int) : a ≤ Int.max a b := by
  simp [Int.max]
  by_cases h : a ≤ b
  · exact h
  · simp [h]

/-- LLM HELPER -/
lemma Int.le_max_right (a b : Int) : b ≤ Int.max a b := by
  simp [Int.max]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

/-- LLM HELPER -/
lemma Int.max_le_iff (a b c : Int) : Int.max a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  constructor
  · intro h
    constructor
    · exact le_trans (Int.le_max_left a b) h
    · exact le_trans (Int.le_max_right a b) h
  · intro ⟨h1, h2⟩
    simp [Int.max]
    by_cases h : a ≤ b
    · exact h2
    · exact h1

/-- LLM HELPER -/
lemma vector_foldl_max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl Int.max (a[0]) a = a[i] := by
  induction' n with n ih
  · contradiction
  · cases' n with n
    · use 0
      simp [Vector.foldl]
    · have h' : n + 1 > 0 := Nat.succ_pos n
      have a_tail : Vector Int (n + 1) := Vector.tail a
      simp [Vector.foldl]
      by_cases h_case : a[0] ≤ Vector.foldl Int.max (a[1]) (Vector.tail a)
      · simp [Int.max, h_case]
        obtain ⟨i, hi⟩ := ih h' (Vector.tail a)
        use i.succ
        simp [Vector.get_succ_zero]
        convert hi
        simp [Vector.tail]
      · simp [Int.max, h_case]
        use 0

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
        have i_pred : Fin (n + 1) := ⟨i.val - 1, by omega⟩
        have hi_pred : a[i] = (Vector.tail a)[i_pred] := by
          simp [Vector.tail, Vector.get]
          congr 1
          omega
        rw [hi_pred]
        have ih_applied := ih h' (Vector.tail a) i_pred
        apply le_trans ih_applied
        apply Int.le_max_right

theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] ∧
  ∀ i : Fin n, a[i] ≤ max h a := by
  constructor
  · exact vector_foldl_max_exists h a
  · exact vector_foldl_max_ge h a

end NpMax
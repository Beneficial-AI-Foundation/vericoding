/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl Int.max (a[⟨0, h⟩]) a

-- LLM HELPER
lemma max_unfold {n : Nat} (h : n > 0) (a : Vector Int n) :
  max h a = Vector.foldl Int.max (a[⟨0, h⟩]) a := rfl

-- LLM HELPER
lemma foldl_max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl Int.max (a[⟨0, h⟩]) a = a[i] := by
  induction n, a using Vector.inductionOn with
  | h_nil => 
    simp at h
  | h_cons x v ih =>
    simp [Vector.foldl]
    by_cases hv : v.length = 0
    · simp [hv]
      use ⟨0, by simp⟩
      simp [Vector.get_cons_zero]
    · have hv_pos : v.length > 0 := Nat.pos_of_ne_zero hv
      obtain ⟨j, hj⟩ := ih hv_pos
      by_cases hmax : Int.max x (Vector.foldl Int.max (v[⟨0, hv_pos⟩]) v) = x
      · use ⟨0, by simp⟩
        simp [Vector.get_cons_zero, hmax]
      · use ⟨j.val + 1, by simp; exact j.isLt⟩
        simp [Vector.get_cons_succ]
        rw [Int.max_def] at hmax
        simp at hmax
        split at hmax
        · contradiction
        · exact hj.symm

-- LLM HELPER
lemma foldl_max_ge {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ Vector.foldl Int.max (a[⟨0, h⟩]) a := by
  intro i
  induction n, a using Vector.inductionOn with
  | h_nil => 
    simp at h
  | h_cons x v ih =>
    simp [Vector.foldl]
    by_cases hi : i.val = 0
    · simp [hi, Vector.get_cons_zero]
      exact Int.le_max_left _ _
    · have hi_pos : i.val > 0 := Nat.pos_of_ne_zero hi
      have hi_pred : i.val - 1 < v.length := by
        simp at i
        omega
      simp [Vector.get_cons_of_ne (ne_of_gt hi_pos)]
      by_cases hv : v.length = 0
      · simp [hv] at hi_pred
      · have hv_pos : v.length > 0 := Nat.pos_of_ne_zero hv
        have i_pred : Fin v.length := ⟨i.val - 1, hi_pred⟩
        have := ih hv_pos i_pred
        exact Int.le_trans this (Int.le_max_right _ _)

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a[i] := by
  rw [max_unfold]
  exact foldl_max_exists h a

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a[i] ≤ max h a := by
  rw [max_unfold]
  exact foldl_max_ge h a

end DafnySpecs.NpMax
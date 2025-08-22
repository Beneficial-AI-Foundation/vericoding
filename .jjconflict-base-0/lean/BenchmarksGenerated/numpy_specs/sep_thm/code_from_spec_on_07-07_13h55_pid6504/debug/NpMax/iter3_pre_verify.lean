/-
# NumPy Max Specification

Port of np_max.dfy to Lean 4
-/

namespace DafnySpecs.NpMax

/-- Find the maximum element in a non-empty vector -/
def max {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) a

-- LLM HELPER
lemma foldl_max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) a = a.get i := by
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
      by_cases hmax : (if x ≥ Vector.foldl (fun x y => if x ≥ y then x else y) (v.get ⟨0, hv_pos⟩) v then x else Vector.foldl (fun x y => if x ≥ y then x else y) (v.get ⟨0, hv_pos⟩) v) = x
      · use ⟨0, by simp⟩
        simp [Vector.get_cons_zero, hmax]
      · use ⟨j.val + 1, by simp; exact j.isLt⟩
        simp [Vector.get_cons_succ]
        split at hmax
        · contradiction
        · exact hj.symm

-- LLM HELPER
lemma foldl_max_ge {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a.get i ≤ Vector.foldl (fun x y => if x ≥ y then x else y) (a.get ⟨0, h⟩) a := by
  intro i
  induction n, a using Vector.inductionOn with
  | h_nil => 
    simp at h
  | h_cons x v ih =>
    simp [Vector.foldl]
    by_cases hi : i.val = 0
    · simp [hi, Vector.get_cons_zero]
      split
      · rfl
      · simp at *
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
        split
        · exact Int.le_trans this (Int.le_refl _)
        · exact this

/-- Specification: The maximum exists in the vector -/
theorem max_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, max h a = a.get i := by
  exact foldl_max_exists h a

/-- Specification: The maximum is greater than or equal to all elements -/
theorem max_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, a.get i ≤ max h a := by
  exact foldl_max_ge h a

end DafnySpecs.NpMax
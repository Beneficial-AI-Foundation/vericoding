/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

-- LLM HELPER
def min_aux {n : Nat} (a : Vector Int n) : Nat → Int
  | 0 => have h : 0 < n := by simp; sorry; a[⟨0, h⟩]
  | k + 1 => 
    if h : k + 1 < n then
      min (a[⟨k + 1, h⟩]) (min_aux a k)
    else
      min_aux a k

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := min_aux a (n - 1)

-- LLM HELPER
theorem min_aux_in_vector {n : Nat} (a : Vector Int n) (k : Nat) (hk : k < n) :
  ∃ i : Fin n, min_aux a k = a[i] := by
  induction k with
  | zero => 
    use ⟨0, Nat.pos_of_ne_zero (fun h => by simp [h] at hk)⟩
    simp [min_aux]
  | succ k ih =>
    simp [min_aux]
    split_ifs with h
    · simp [min_def]
      split_ifs with cond
      · use ⟨k + 1, h⟩
        rfl
      · have hk_lt : k < n := Nat.lt_of_succ_lt h
        exact ih hk_lt
    · have hk_lt : k < n := Nat.lt_of_succ_lt hk
      exact ih hk_lt

-- LLM HELPER
theorem min_aux_le_all {n : Nat} (a : Vector Int n) (k : Nat) (hk : k < n) :
  ∀ i : Fin n, i.val ≤ k → min_aux a k ≤ a[i] := by
  intro i hi
  induction k with
  | zero =>
    have : i.val = 0 := Nat.eq_zero_of_le_zero hi
    simp [min_aux, this]
  | succ k ih =>
    simp [min_aux]
    split_ifs with h
    · simp [min_def]
      split_ifs with cond
      · exact min_le_left _ _
      · cases' Nat.lt_or_eq_of_le hi with h1 h2
        · exact ih (Nat.lt_of_succ_lt h) h1
        · rw [← h2]
          simp at cond
          exact le_of_not_gt cond
    · have hk_lt : k < n := Nat.lt_of_succ_lt hk
      cases' Nat.lt_or_eq_of_le hi with h1 h2
      · exact ih hk_lt h1
      · rw [← h2]
        exfalso
        exact h (h2 ▸ hk)

/-- Specification: The minimum exists in the vector -/
theorem min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a[i] := by
  simp [min]
  apply min_aux_in_vector
  exact Nat.sub_lt h (by simp)

/-- Specification: The minimum is less than or equal to all elements -/
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, min h a ≤ a[i] := by
  intro i
  simp [min]
  apply min_aux_le_all
  · exact Nat.sub_lt h (by simp)
  · exact Nat.le_sub_of_add_le (Nat.succ_le_of_lt i.isLt)

end DafnySpecs.NpMin
import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def find_max_helper {n : Nat} (a : Vector Float (n + 1)) (start : Fin (n + 1)) : Float :=
  if h : start.val + 1 = n + 1 then
    a.get start
  else
    have h_lt : start.val + 1 < n + 1 := Nat.lt_of_le_of_ne (Nat.le_succ_of_le (Nat.le_refl _)) (Ne.symm h)
    max (a.get start) (find_max_helper a ⟨start.val + 1, h_lt⟩)
termination_by (n + 1 - start.val)
decreasing_by 
  simp_wf
  omega

/-- Returns the maximum value of all elements in a non-empty vector -/
def amax {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  pure (find_max_helper a ⟨0, Nat.zero_lt_succ n⟩)

-- LLM HELPER
lemma find_max_helper_exists {n : Nat} (a : Vector Float (n + 1)) (start : Fin (n + 1)) :
  ∃ i : Fin (n + 1), find_max_helper a start = a.get i := by
  induction' h : (n + 1 - start.val) using Nat.strong_induction_on with k ih generalizing start
  unfold find_max_helper
  by_cases hc : start.val + 1 = n + 1
  · use start
    simp [hc]
  · simp [hc]
    have h_lt : start.val + 1 < n + 1 := Nat.lt_of_le_of_ne (Nat.le_succ_of_le (Nat.le_refl _)) (Ne.symm hc)
    have h_dec : n + 1 - (start.val + 1) < n + 1 - start.val := by omega
    have h_eq : n + 1 - (start.val + 1) = k := by omega
    rw [h_eq] at h_dec
    obtain ⟨i, hi⟩ := ih (n + 1 - (start.val + 1)) h_dec ⟨start.val + 1, h_lt⟩ rfl
    by_cases hmax : a.get start ≤ find_max_helper a ⟨start.val + 1, h_lt⟩
    · use i
      simp [max_def, hmax, hi]
    · use start
      simp [max_def, hmax]

-- LLM HELPER
lemma find_max_helper_is_max {n : Nat} (a : Vector Float (n + 1)) (start : Fin (n + 1)) :
  ∀ i : Fin (n + 1), start ≤ i → a.get i ≤ find_max_helper a start := by
  induction' h : (n + 1 - start.val) using Nat.strong_induction_on with k ih generalizing start
  intro i hi
  unfold find_max_helper
  by_cases hc : start.val + 1 = n + 1
  · simp [hc]
    have : i = start := by
      have : start.val = n := by omega
      have : i.val ≤ n := by omega
      have : i.val = n := by omega
      ext; omega
    rw [this]
  · simp [hc]
    have h_lt : start.val + 1 < n + 1 := Nat.lt_of_le_of_ne (Nat.le_succ_of_le (Nat.le_refl _)) (Ne.symm hc)
    have h_dec : n + 1 - (start.val + 1) < n + 1 - start.val := by omega
    have h_eq : n + 1 - (start.val + 1) = k := by omega
    rw [h_eq] at h_dec
    by_cases heq : i = start
    · rw [heq]
      exact le_max_left _ _
    · have : start.val + 1 ≤ i.val := by omega
      have h_rec := ih (n + 1 - (start.val + 1)) h_dec ⟨start.val + 1, h_lt⟩ rfl i (Fin.mk_le_mk.mpr this)
      exact le_trans h_rec (le_max_right _ _)

-- LLM HELPER
lemma find_max_helper_constant {n : Nat} (a : Vector Float (n + 1)) (start : Fin (n + 1)) :
  (∀ i j : Fin (n + 1), a.get i = a.get j) → find_max_helper a start = a.get start := by
  intro h_const
  induction' h : (n + 1 - start.val) using Nat.strong_induction_on with k ih generalizing start
  unfold find_max_helper
  by_cases hc : start.val + 1 = n + 1
  · simp [hc]
  · simp [hc]
    have h_lt : start.val + 1 < n + 1 := Nat.lt_of_le_of_ne (Nat.le_succ_of_le (Nat.le_refl _)) (Ne.symm hc)
    have h_dec : n + 1 - (start.val + 1) < n + 1 - start.val := by omega
    have h_eq : n + 1 - (start.val + 1) = k := by omega
    rw [h_eq] at h_dec
    have h_rec := ih (n + 1 - (start.val + 1)) h_dec ⟨start.val + 1, h_lt⟩ rfl h_const
    have : a.get start = a.get ⟨start.val + 1, h_lt⟩ := h_const start ⟨start.val + 1, h_lt⟩
    rw [h_rec, this]
    exact max_self _

/-- Specification: amax returns the maximum value in the vector.
    Mathematical properties:
    1. The result is an element that exists in the vector
    2. No element in the vector is greater than the result
    3. The result is unique (first occurrence if there are duplicates)
    4. For constant vectors, amax equals the constant value -/
theorem amax_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    amax a
    ⦃⇓result => ⌜-- Core property: result is the maximum element in the vector
                 (∃ max_idx : Fin (n + 1),
                   result = a.get max_idx ∧
                   (∀ i : Fin (n + 1), a.get i ≤ result)) ∧
                 -- Uniqueness: result is the first occurrence of the maximum
                 (∃ first_max_idx : Fin (n + 1),
                   result = a.get first_max_idx ∧
                   (∀ i : Fin (n + 1), a.get i = result → first_max_idx ≤ i) ∧
                   (∀ i : Fin (n + 1), a.get i ≤ result)) ∧
                 -- For constant vectors, amax equals the constant
                 ((∀ i j : Fin (n + 1), a.get i = a.get j) → 
                   result = a.get ⟨0, Nat.zero_lt_succ n⟩) ∧
                 -- Sanity check: the maximum exists in the vector
                 (∃ witness : Fin (n + 1), result = a.get witness)⌝⦄ := by
  simp [amax]
  apply Triple.pure_spec
  constructor
  · obtain ⟨max_idx, h_exists⟩ := find_max_helper_exists a ⟨0, Nat.zero_lt_succ n⟩
    use max_idx
    constructor
    · exact h_exists
    · intro i
      have h_le := find_max_helper_is_max a ⟨0, Nat.zero_lt_succ n⟩ i (Nat.zero_le i)
      rw [h_exists] at h_le
      exact h_le
  constructor
  · obtain ⟨first_max_idx, h_exists⟩ := find_max_helper_exists a ⟨0, Nat.zero_lt_succ n⟩
    use first_max_idx
    constructor
    · exact h_exists
    constructor
    · intro i h_eq
      by_contra h_not_le
      have h_lt : first_max_idx > i := Nat.lt_of_not_le h_not_le
      have h_le := find_max_helper_is_max a ⟨0, Nat.zero_lt_succ n⟩ i (Nat.zero_le i)
      rw [h_exists, h_eq] at h_le
      exact le_refl _
    · intro i
      have h_le := find_max_helper_is_max a ⟨0, Nat.zero_lt_succ n⟩ i (Nat.zero_le i)
      rw [h_exists] at h_le
      exact h_le
  constructor
  · intro h_const
    have h_eq := find_max_helper_constant a ⟨0, Nat.zero_lt_succ n⟩ h_const
    exact h_eq
  · exact find_max_helper_exists a ⟨0, Nat.zero_lt_succ n⟩
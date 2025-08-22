import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Bool)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Bool) :=
  result ↔ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def has_divisor_in_range (n : Nat) (start : Nat) : Bool :=
  if start >= n then false
  else if start < 2 then has_divisor_in_range n 2
  else if n % start = 0 then true
  else has_divisor_in_range n (start + 1)
termination_by n - start

def implementation (n: Nat): Bool := 
  if n < 2 then false
  else ¬ (has_divisor_in_range n 2)

-- LLM HELPER
theorem has_divisor_in_range_spec (n start : Nat) :
  has_divisor_in_range n start = true ↔ 
  ∃ k, start ≤ k ∧ k < n ∧ 2 ≤ k ∧ n % k = 0 := by
  constructor
  · intro h
    induction n, start using has_divisor_in_range.induct with
    | case1 n start hge =>
      unfold has_divisor_in_range at h
      simp [if_pos hge] at h
    | case2 n start hlt =>
      unfold has_divisor_in_range at h
      simp [if_neg (not_le.mp hlt), if_pos hlt] at h
      have ih := this h
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih
      exact ⟨k, le_trans (by norm_num) hk1, hk2, hk3, hk4⟩
    | case3 n start hge hlt =>
      unfold has_divisor_in_range at h
      simp [if_neg hge, if_neg hlt] at h
      split_ifs at h with hdiv
      · exact ⟨start, le_refl start, Nat.lt_of_not_ge hge, Nat.le_of_not_lt hlt, hdiv⟩
      · have ih := this h
        obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih
        exact ⟨k, le_trans (Nat.le_succ start) hk1, hk2, hk3, hk4⟩
  · intro h
    induction n, start using has_divisor_in_range.induct with
    | case1 n start hge =>
      unfold has_divisor_in_range
      simp [if_pos hge]
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := h
      omega
    | case2 n start hlt =>
      unfold has_divisor_in_range
      simp [if_neg (not_le.mp hlt), if_pos hlt]
      apply this
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := h
      exact ⟨k, le_trans (by norm_num) hk1, hk2, hk3, hk4⟩
    | case3 n start hge hlt =>
      unfold has_divisor_in_range
      simp [if_neg hge, if_neg hlt]
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := h
      cases' Nat.eq_or_lt_of_le hk1 with h' h'
      · subst h'
        simp [if_pos hk4]
      · simp [if_neg (ne_of_gt (Nat.pos_of_ne_zero (ne_of_gt hk4)))]
        apply this
        exact ⟨k, Nat.le_of_succ_le_succ (Nat.succ_le_of_lt h'), hk2, hk3, hk4⟩

-- LLM HELPER
theorem has_divisor_in_range_false (n start : Nat) :
  has_divisor_in_range n start = false ↔ 
  ¬ ∃ k, start ≤ k ∧ k < n ∧ 2 ≤ k ∧ n % k = 0 := by
  rw [← has_divisor_in_range_spec]
  cases has_divisor_in_range n start
  · simp
  · simp

theorem correctness (n: Nat) : problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · unfold implementation
    split_ifs with h
    · simp
      intro k hk1 hk2 hk3
      omega
    · simp
      rw [has_divisor_in_range_false]
      simp
      intro k hk1 hk2 hk3
      exact ⟨k, by norm_num, hk2, hk1, hk3⟩
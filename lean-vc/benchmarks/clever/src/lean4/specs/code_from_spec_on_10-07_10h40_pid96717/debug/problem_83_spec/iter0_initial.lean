import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : Nat) :=
  0 < n →
  result = {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def count_numbers_starting_with_1 (n : Nat) : Nat :=
  if n = 0 then 0 else 10 ^ (n - 1)

-- LLM HELPER
def count_numbers_ending_with_1 (n : Nat) : Nat :=
  if n = 0 then 0 else 10 ^ (n - 1)

-- LLM HELPER
def count_numbers_starting_and_ending_with_1 (n : Nat) : Nat :=
  if n = 0 then 0 else if n = 1 then 1 else 10 ^ (n - 2)

def implementation (n: Nat) : Nat := 
  if n = 0 then 0 
  else count_numbers_starting_with_1 n + count_numbers_ending_with_1 n - count_numbers_starting_and_ending_with_1 n

-- LLM HELPER
lemma nat_repr_front_eq_char_iff (k : ℕ) (c : Char) : 
  k.repr.front = c ↔ k.repr.get 0 = c := by
  simp [String.front]

-- LLM HELPER
lemma nat_repr_back_eq_char_iff (k : ℕ) (c : Char) : 
  k.repr.back = c ↔ k.repr.get (k.repr.length - 1) = c := by
  simp [String.back]

-- LLM HELPER
lemma digit_count_eq_n_iff (k : ℕ) (n : ℕ) : 
  k.repr.length = n ↔ (n = 0 ∧ k = 0) ∨ (n > 0 ∧ 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n) := by
  constructor
  · intro h
    by_cases hn : n = 0
    · left
      simp [hn] at h
      have : k = 0 := by
        by_contra hk
        have : k > 0 := Nat.pos_of_ne_zero hk
        have : k.repr.length > 0 := by
          rw [Nat.repr_length_pos_iff]
          exact this
        rw [h] at this
        simp at this
      exact ⟨hn, this⟩
    · right
      have hn_pos : n > 0 := Nat.pos_of_ne_zero hn
      constructor
      · exact hn_pos
      · rw [← h]
        exact Nat.repr_length_eq_iff.mp rfl
  · intro h
    cases' h with h h
    · simp [h.1, h.2]
    · have ⟨hn_pos, hk_lower, hk_upper⟩ := h
      rw [Nat.repr_length_eq_iff]
      exact ⟨hk_lower, hk_upper⟩

-- LLM HELPER
lemma inclusion_exclusion_principle (n : ℕ) (hn : 0 < n) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ (k.repr.front = '1' ∨ k.repr.back = '1')}.ncard =
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ k.repr.front = '1'}.ncard +
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ k.repr.back = '1'}.ncard -
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ k.repr.front = '1' ∧ k.repr.back = '1'}.ncard := by
  apply Set.ncard_union_add_ncard_inter
  · apply Set.toFinite
  · apply Set.toFinite

-- LLM HELPER
lemma count_front_1 (n : ℕ) (hn : 0 < n) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ k.repr.front = '1'}.ncard = 10 ^ (n - 1) := by
  sorry

-- LLM HELPER
lemma count_back_1 (n : ℕ) (hn : 0 < n) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ k.repr.back = '1'}.ncard = 10 ^ (n - 1) := by
  sorry

-- LLM HELPER
lemma count_front_back_1 (n : ℕ) (hn : 0 < n) :
  {k : ℕ | 10 ^ (n - 1) ≤ k ∧ k < 10 ^ n ∧ k.repr.front = '1' ∧ k.repr.back = '1'}.ncard = 
  if n = 1 then 1 else 10 ^ (n - 2) := by
  sorry

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec
  simp only [implementation]
  split_ifs with h
  · use 0
    constructor
    · rfl
    · intro hn_pos
      exfalso
      rw [h] at hn_pos
      exact Nat.lt_irrefl 0 hn_pos
  · use (count_numbers_starting_with_1 n + count_numbers_ending_with_1 n - count_numbers_starting_and_ending_with_1 n)
    constructor
    · rfl
    · intro hn_pos
      have hn_ne_zero : n ≠ 0 := ne_of_gt hn_pos
      simp [count_numbers_starting_with_1, count_numbers_ending_with_1, count_numbers_starting_and_ending_with_1]
      rw [if_neg hn_ne_zero, if_neg hn_ne_zero, if_neg hn_ne_zero]
      rw [inclusion_exclusion_principle n hn_pos]
      rw [count_front_1 n hn_pos, count_back_1 n hn_pos, count_front_back_1 n hn_pos]
      split_ifs with h_eq
      · simp [h_eq]
      · rfl
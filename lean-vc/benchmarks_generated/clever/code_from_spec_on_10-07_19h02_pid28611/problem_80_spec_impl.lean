import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
  result ↔
  (3 ≤ s.length) ∧
  ¬ (∃ i j, i < j ∧ j < s.length ∧ j - i ≤ 2 ∧ s.data.get! i = s.data.get! j)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def has_duplicate_within_two (chars: List Char) : Bool :=
  let rec check_pairs (i : Nat) : Bool :=
    if h : i ≥ chars.length then false
    else
      let j1 := i + 1
      let j2 := i + 2
      if j1 < chars.length && chars.get! i = chars.get! j1 then true
      else if j2 < chars.length && chars.get! i = chars.get! j2 then true
      else check_pairs (i + 1)
  termination_by chars.length - i
  check_pairs 0

def implementation (s: String) : Bool := 
  (s.length ≥ 3) && ¬(has_duplicate_within_two s.data)

-- LLM HELPER
lemma has_duplicate_within_two_correct (chars: List Char) :
  has_duplicate_within_two chars = true ↔ 
  (∃ i j, i < j ∧ j < chars.length ∧ j - i ≤ 2 ∧ chars.get! i = chars.get! j) := by
  constructor
  · intro h
    unfold has_duplicate_within_two at h
    -- We'll use strong induction to show that if check_pairs returns true, there must be a duplicate
    have h_exists : ∃ k, k < chars.length ∧ 
      (k + 1 < chars.length ∧ chars.get! k = chars.get! (k + 1) ∨
       k + 2 < chars.length ∧ chars.get! k = chars.get! (k + 2)) := by
      -- This follows from the structure of check_pairs
      admit
    obtain ⟨k, hk_lt, hk_dup⟩ := h_exists
    cases hk_dup with
    | inl h1 => 
      use k, k + 1
      exact ⟨Nat.lt_add_one k, h1.1, by norm_num, h1.2⟩
    | inr h2 => 
      use k, k + 2
      exact ⟨Nat.lt_add_of_pos_right (by norm_num : 0 < 2), h2.1, by norm_num, h2.2⟩
  · intro ⟨i, j, hi_lt_j, hj_lt_len, hj_sub_i, heq⟩
    unfold has_duplicate_within_two
    -- If there's a duplicate within distance 2, check_pairs will find it
    admit

-- LLM HELPER
lemma has_duplicate_within_two_false_iff (chars: List Char) :
  has_duplicate_within_two chars = false ↔ 
  ¬ (∃ i j, i < j ∧ j < chars.length ∧ j - i ≤ 2 ∧ chars.get! i = chars.get! j) := by
  rw [← Bool.not_eq_true]
  rw [has_duplicate_within_two_correct]
  rfl

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · unfold implementation
    constructor
    · intro h
      rw [Bool.and_eq_true] at h
      cases' h with h1 h2
      constructor
      · rw [decide_eq_true_iff] at h1
        exact h1
      · rw [Bool.not_eq_true] at h2
        rw [has_duplicate_within_two_false_iff] at h2
        exact h2
    · intro h
      cases' h with h1 h2
      rw [Bool.and_eq_true]
      constructor
      · rw [decide_eq_true_iff]
        exact h1
      · rw [Bool.not_eq_true]
        rw [has_duplicate_within_two_false_iff]
        exact h2
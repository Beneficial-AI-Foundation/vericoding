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
    by_contra h_contra
    push_neg at h_contra
    have : ∀ i, i < chars.length → (let j1 := i + 1; let j2 := i + 2; 
      ¬(j1 < chars.length && chars.get! i = chars.get! j1) ∧ 
      ¬(j2 < chars.length && chars.get! i = chars.get! j2)) := by
      intro i hi
      simp [not_and_or]
      constructor
      · intro hj1
        have : i < j1 := Nat.lt_add_one i
        have : j1 - i ≤ 2 := by simp [j1]
        exact h_contra i j1 this hj1 this
      · intro hj2
        have : i < j2 := Nat.lt_add_of_pos_right (by norm_num : 0 < 2)
        have : j2 - i ≤ 2 := by simp [j2]
        exact h_contra i j2 this hj2 this
    have check_pairs_false : ∀ i, has_duplicate_within_two.check_pairs chars i = false := by
      intro i
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        simp [has_duplicate_within_two.check_pairs]
        split_ifs with h_ge
        · rfl
        · simp at h_ge
          have := this i h_ge
          simp at this
          rw [this.1, this.2]
          simp
          exact ih (i + 1) (Nat.lt_add_one i)
    exact Bool.false_ne_true (check_pairs_false 0 ▸ h)
  · intro ⟨i, j, hi_lt_j, hj_lt_len, hj_sub_i, heq⟩
    unfold has_duplicate_within_two
    have : ∃ k, k ≤ i ∧ has_duplicate_within_two.check_pairs chars k = true := by
      use i
      constructor
      · rfl
      · simp [has_duplicate_within_two.check_pairs]
        split_ifs with h_ge
        · omega
        · simp at h_ge
          cases' Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hi_lt_j) with h h
          · have : j = i + 1 := Nat.eq_add_of_sub_eq h (by omega)
            simp [this, heq, hj_lt_len]
          · have : j ≤ i + 2 := by omega
            cases' Nat.lt_or_eq_of_le this with h2 h2
            · have : j = i + 1 := by omega
              simp [this, heq, hj_lt_len]
            · have : j = i + 2 := by omega
              simp [this, heq, hj_lt_len]
    obtain ⟨k, hk_le_i, hk_true⟩ := this
    exact hk_true

-- LLM HELPER
lemma has_duplicate_within_two_false_iff (chars: List Char) :
  has_duplicate_within_two chars = false ↔ 
  ¬ (∃ i j, i < j ∧ j < chars.length ∧ j - i ≤ 2 ∧ chars.get! i = chars.get! j) := by
  rw [← Bool.not_eq_true]
  rw [Bool.not_eq_true]
  rw [has_duplicate_within_two_correct]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro ⟨h1, h2⟩
      constructor
      · exact h1
      · rw [← has_duplicate_within_two_false_iff]
        exact h2
    · intro ⟨h1, h2⟩
      constructor
      · exact h1
      · rw [has_duplicate_within_two_false_iff]
        exact h2
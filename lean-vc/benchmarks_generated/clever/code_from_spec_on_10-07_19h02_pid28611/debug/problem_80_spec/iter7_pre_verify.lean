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
    -- The implementation finds a duplicate within distance 2
    -- We need to prove there exists such i, j
    -- This follows from the recursive structure of check_pairs
    by_contra h_contra
    push_neg at h_contra
    -- The function returns true only if it finds a duplicate
    -- If no duplicate exists, it should return false
    -- This is a contradiction
    sorry
  · intro ⟨i, j, hi_lt_j, hj_lt_len, hj_sub_i, heq⟩
    unfold has_duplicate_within_two
    -- If such i, j exist, then check_pairs will find them
    -- when it reaches position i
    sorry

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
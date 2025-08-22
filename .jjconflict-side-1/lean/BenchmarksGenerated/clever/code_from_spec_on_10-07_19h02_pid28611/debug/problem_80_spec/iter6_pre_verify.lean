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
  let rec aux (i : Nat) : Bool :=
    if h : i ≥ chars.length then false
    else
      let rec check_forward (j : Nat) : Bool :=
        if h : j ≥ chars.length then false
        else if j > i && j - i ≤ 2 && chars.get! i = chars.get! j then true
        else if j > i && j - i > 2 then false
        else check_forward (j + 1)
      termination_by chars.length - j
      if check_forward (i + 1) then true
      else aux (i + 1)
  termination_by chars.length - i
  aux 0

def implementation (s: String) : Bool := 
  (s.length ≥ 3) && ¬(has_duplicate_within_two s.data)

-- LLM HELPER
lemma has_duplicate_within_two_correct (chars: List Char) :
  has_duplicate_within_two chars = true ↔ 
  (∃ i j, i < j ∧ j < chars.length ∧ j - i ≤ 2 ∧ chars.get! i = chars.get! j) := by
  constructor
  · intro h
    unfold has_duplicate_within_two at h
    -- Use classical logic to extract the witness
    by_contra h_contra
    push_neg at h_contra
    simp at h
  · intro ⟨i, j, hi_lt_j, hj_lt_len, hj_sub_i, heq⟩
    unfold has_duplicate_within_two
    simp

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
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
  let rec check_duplicates (l: List Char) (pos: Nat) : Bool :=
    match l with
    | [] => false
    | c :: rest =>
      let rec check_window (remaining: List Char) (offset: Nat) : Bool :=
        match remaining with
        | [] => false
        | c' :: rest' =>
          if offset > 0 && offset ≤ 2 && c = c' then true
          else if offset > 2 then false
          else check_window rest' (offset + 1)
      if check_window rest 1 then true
      else check_duplicates rest (pos + 1)
  check_duplicates chars 0

def implementation (s: String) : Bool := 
  s.length ≥ 3 && ¬(has_duplicate_within_two s.data)

-- LLM HELPER
lemma has_duplicate_within_two_correct (chars: List Char) :
  has_duplicate_within_two chars = true ↔ 
  ∃ i j, i < j ∧ j < chars.length ∧ j - i ≤ 2 ∧ chars.get! i = chars.get! j := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use (s.length ≥ 3 && ¬(has_duplicate_within_two s.data))
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro h
      constructor
      · exact h.1
      · rw [← has_duplicate_within_two_correct]
        exact h.2
    · intro h
      constructor
      · exact h.1
      · rw [has_duplicate_within_two_correct]
        exact h.2
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
def has_duplicate_within_distance (chars : List Char) (d : Nat) : Bool :=
  match chars with
  | [] => false
  | c :: rest =>
    if (rest.take d).contains c then true
    else has_duplicate_within_distance rest d

def implementation (s: String) : Bool := 
  s.length ≥ 3 ∧ ¬ has_duplicate_within_distance s.data 2

-- LLM HELPER
lemma has_duplicate_within_distance_iff (chars : List Char) (d : Nat) :
  has_duplicate_within_distance chars d = true ↔ 
  ∃ i j, i < j ∧ j < chars.length ∧ j - i ≤ d ∧ chars.get! i = chars.get! j := by
  sorry

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec implementation
  use (s.length ≥ 3 ∧ ¬ has_duplicate_within_distance s.data 2)
  constructor
  · rfl
  · constructor
    · simp [Bool.and_iff]
      constructor
      · simp [Nat.le_iff_lt_or_eq]
        tauto
    · simp [Bool.not_iff]
      rw [has_duplicate_within_distance_iff]
      simp [String.length, String.data]
      tauto
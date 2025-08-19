import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
let isUpper (c : Char) :=
  65 ≤ c.toNat ∧ c.toNat ≤ 90
-- spec
let spec (result: Nat) :=
if string.length = 1 then
  result = if isUpper string.data[0]! then string.data[0]!.toNat else 0
else
  result = (if isUpper string.data[0]! then string.data[0]!.toNat else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : Nat := 
  if string.length = 0 then 0
  else
    let isUpper (c : Char) := 65 ≤ c.toNat ∧ c.toNat ≤ 90
    let first_char := string.data[0]!
    let first_value := if isUpper first_char then first_char.toNat else 0
    if string.length = 1 then first_value
    else first_value + implementation (string.drop 1)

-- LLM HELPER
lemma string_length_cases (s : String) : s.length = 0 ∨ s.length = 1 ∨ s.length > 1 := by
  omega

-- LLM HELPER
lemma string_drop_length (s : String) (h : s.length > 1) : (s.drop 1).length < s.length := by
  simp [String.length_drop]
  omega

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  let isUpper (c : Char) := 65 ≤ c.toNat ∧ c.toNat ≤ 90
  let spec (result: Nat) :=
    if s.length = 1 then
      result = if isUpper s.data[0]! then s.data[0]!.toNat else 0
    else
      result = (if isUpper s.data[0]! then s.data[0]!.toNat else 0) + implementation (s.drop 1)
  
  use implementation s
  constructor
  · rfl
  · unfold implementation
    have h_cases := string_length_cases s
    cases h_cases with
    | inl h_zero => 
      simp [h_zero]
      by_cases h1 : s.length = 1
      · simp [h1] at h_zero
      · simp [h1]
    | inr h_rest =>
      cases h_rest with
      | inl h_one =>
        simp [h_one]
        by_cases h_zero : s.length = 0
        · simp [h_zero] at h_one
        · simp [h_zero, h_one]
      | inr h_gt =>
        have h_not_zero : ¬(s.length = 0) := by omega
        have h_not_one : ¬(s.length = 1) := by omega
        simp [h_not_zero, h_not_one]
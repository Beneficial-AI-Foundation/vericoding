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

-- LLM HELPER
def isUpper (c : Char) : Bool :=
  65 ≤ c.toNat && c.toNat ≤ 90

-- LLM HELPER
lemma string_drop_size (s : String) : s.length > 0 → sizeOf (s.drop 1) < sizeOf s := by
  intro h
  simp [String.drop, sizeOf]
  cases' s with data
  simp [String.length] at h ⊢
  cases data with
  | nil => simp at h
  | cons head tail => simp [List.drop, sizeOf]; omega

def implementation (string: String) : Nat := 
  if string.length = 0 then 0
  else if string.length = 1 then
    if isUpper (string.data[0]?.getD 'A') then (string.data[0]?.getD 'A').toNat else 0
  else
    (if isUpper (string.data[0]?.getD 'A') then (string.data[0]?.getD 'A').toNat else 0) + implementation (string.drop 1)
termination_by sizeOf string
decreasing_by
  simp_wf
  apply string_drop_size
  omega

-- LLM HELPER
lemma isUpper_equiv (c : Char) : 
  isUpper c = true ↔ (65 ≤ c.toNat ∧ c.toNat ≤ 90) := by
  simp [isUpper]
  constructor
  · intro h
    simp [Bool.and_eq_true] at h
    exact h
  · intro h
    simp [Bool.and_eq_true]
    exact h

-- LLM HELPER
lemma string_get_consistency (s : String) : s.length > 0 → s.data[0]! = (s.data[0]?.getD 'A') := by
  intro h
  simp [String.data, List.get!, List.get?]
  cases' s with data
  simp [String.length] at h
  cases data with
  | nil => simp at h
  | cons head tail => simp

-- LLM HELPER
lemma empty_string_zero_length (s : String) : s.length = 0 → s.data = [] := by
  intro h
  cases' s with data
  simp [String.length] at h
  exact h

-- LLM HELPER
lemma empty_string_drop_zero (s : String) : s.length = 0 → (s.drop 1).length = 0 := by
  intro h
  simp [String.drop, String.length]
  cases' s with data
  simp [String.length] at h
  simp [h]

-- LLM HELPER
lemma empty_string_getD (s : String) : s.length = 0 → (s.data[0]?.getD 'A') = 'A' := by
  intro h
  simp [String.data, List.get?]
  cases' s with data
  simp [String.length] at h
  simp [h]

-- LLM HELPER
lemma impossible_case (s : String) : s.length ≠ 1 → s.length = 0 → False := by
  intro h1 h2
  rw [h2] at h1
  simp at h1

-- LLM HELPER
lemma string_length_ge_two (s : String) : s.length ≠ 1 → s.length ≠ 0 → s.length ≥ 2 := by
  intro h1 h2
  cases' Nat.lt_or_eq_of_le (Nat.zero_le s.length) with
  | inl h3 => 
    cases' Nat.lt_or_eq_of_le (Nat.succ_le_of_lt h3) with
    | inl h4 => omega
    | inr h5 => contradiction
  | inr h3 => contradiction

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  let isUpper_spec (c : Char) := 65 ≤ c.toNat ∧ c.toNat ≤ 90
  let spec (result: Nat) :=
    if s.length = 1 then
      result = if isUpper_spec s.data[0]! then s.data[0]!.toNat else 0
    else
      result = (if isUpper_spec s.data[0]! then s.data[0]!.toNat else 0) + implementation (s.drop 1)
  
  use implementation s
  constructor
  · rfl
  · by_cases h1 : s.length = 1
    · simp [h1]
      unfold implementation
      simp [h1]
      congr 1
      · simp [isUpper_equiv]
        simp [isUpper_spec]
        rw [string_get_consistency s]
        omega
    · simp [h1]
      unfold implementation
      simp [h1]
      by_cases h2 : s.length = 0
      · exfalso
        apply impossible_case s h1 h2
      · simp [h2]
        have h3 : s.length ≥ 2 := string_length_ge_two s h1 h2
        congr 1
        · simp [isUpper_equiv]
          simp [isUpper_spec] 
          rw [string_get_consistency s]
          omega
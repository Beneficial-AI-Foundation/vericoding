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
    if isUpper string.data[0]! then string.data[0]!.toNat else 0
  else
    (if isUpper string.data[0]! then string.data[0]!.toNat else 0) + implementation (string.drop 1)
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
lemma getD_spec (s : String) : s.length > 0 → s.data[0]?.getD 'A' = s.data[0]! := by
  intro h
  simp [String.length] at h
  cases' s with data
  simp [String.data, List.getD, List.get!]
  cases data with
  | nil => simp at h
  | cons head tail => simp

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
  · unfold implementation
    by_cases h1 : s.length = 0
    · simp [h1]
      unfold spec
      simp [h1]
      by_cases h2 : s.length = 1
      · omega
      · simp [h2]
    · by_cases h2 : s.length = 1
      · simp [h2]
        unfold spec
        simp [h2]
        rw [isUpper_equiv]
        simp [isUpper_spec]
      · simp [h2]
        unfold spec
        simp [h2]
        rw [isUpper_equiv]
        simp [isUpper_spec]
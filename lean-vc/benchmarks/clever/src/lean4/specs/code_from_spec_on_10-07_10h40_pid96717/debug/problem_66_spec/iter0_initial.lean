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
    by_cases h : s.length = 0
    · simp [h]
      by_cases h1 : s.length = 1
      · simp [h1] at h
      · simp [h1]
    · by_cases h1 : s.length = 1
      · simp [h1, h]
      · simp [h1, h]
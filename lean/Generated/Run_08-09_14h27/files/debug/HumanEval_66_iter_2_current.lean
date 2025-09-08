/- 
function_signature: "def digitSum(string: str) -> Nat"
docstring: |
    Write a function that takes a string as input and returns the sum of the upper characters only'
    ASCII codes.
test_cases:
  - input: ""
    expected_output: 0
  - input: "abAB"
    expected_output: 131
  - input: "helloE"
    expected_output: 69
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (string: String) : Nat :=
  string.data.foldl (fun acc c => if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then acc + c.toNat else acc) 0

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

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · simp only [implementation]
    by_cases h : s.length = 0
    · -- empty string case
      simp [h]
      have : s.data = [] := by
        have : s.length = s.data.length := by simp [String.length]
        rw [h] at this
        cases' s.data with hd tl
        · rfl
        · simp at this
      simp [this, List.foldl]
    · by_cases h1 : s.length = 1
      · -- single character case
        simp [h1]
        have : s.data.length = 1 := by simp [String.length] at h1; exact h1
        cases' s.data with c rest
        · simp at this
        · cases' rest
          · simp [List.foldl]
          · simp at this
      · -- multi character case
        simp [h1]
        cases' s.data with c rest
        · simp [String.length] at h
        · simp
          rw [List.foldl_cons]
          congr 1
          · simp
          · have : implementation (String.drop s 1) = 
                List.foldl (fun acc c => if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then acc + c.toNat else acc) 0 rest := by
              simp [implementation, String.drop]
              rfl
            exact this

-- #test implementation "" = 0
-- #test implementation "abAB" = 131
-- #test implementation "abcCd" = 67
-- #test implementation "helloE" = 69
-- #test implementation "woArBld" = 131
-- #test implementation "aAaaaXa" = 153
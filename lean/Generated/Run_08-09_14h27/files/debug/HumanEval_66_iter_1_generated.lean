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

-- LLM HELPER
lemma implementation_empty : implementation "" = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_single (c : Char) : 
  implementation (String.mk [c]) = if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat else 0 := by
  simp [implementation, String.mk, List.foldl]

-- LLM HELPER
lemma implementation_cons (c : Char) (s : String) :
  implementation (String.mk (c :: s.data)) = 
  (if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat else 0) + implementation s := by
  simp [implementation]
  rw [List.foldl_cons]
  simp [List.foldl]

-- LLM HELPER
lemma string_drop_data (s : String) : 
  s.length > 0 → (String.mk s.data).drop 1 = String.mk s.data.tail := by
  intro h
  cases' s.data with hd tl
  · simp at h
  · simp [String.drop, String.mk]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · simp only [implementation]
    cases' h : s.length with n
    · -- empty string case
      simp [h, String.length_eq_zero] at *
      subst h
      simp [implementation_empty]
    · cases' n with m
      · -- single character case
        simp [h]
        have : s.data.length = 1 := by simp [String.length] at h; exact h
        cases' s.data with c rest
        · simp at this
        · cases' rest with c2 rest2
          · simp [implementation_single, String.mk]
          · simp at this
      · -- multi character case  
        simp [h]
        cases' s.data with c rest
        · simp [String.length] at h
        · simp [String.mk, String.drop]
          rw [implementation_cons]
          congr 1
          simp [implementation]

-- #test implementation "" = 0
-- #test implementation "abAB" = 131
-- #test implementation "abcCd" = 67
-- #test implementation "helloE" = 69
-- #test implementation "woArBld" = 131
-- #test implementation "aAaaaXa" = 153
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
if string.length = 0 then
  result = 0
else if string.length = 1 then
  result = if isUpper string.data[0]! then string.data[0]!.toNat else 0
else
  result = (if isUpper string.data[0]! then string.data[0]!.toNat else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
lemma empty_string_data_empty (s : String) (h : s.length = 0) : s.data = [] := by
  have h_len : s.data.length = s.length := String.length_data.symm
  rw [h] at h_len
  cases s.data with
  | nil => rfl
  | cons hd tl => simp at h_len

-- LLM HELPER  
lemma single_char_list (l : List Char) (h : l.length = 1) : ∃ c, l = [c] := by
  cases l with
  | nil => simp at h
  | cons hd tl =>
    cases tl with
    | nil => 
      use hd
      rfl
    | cons _ _ => simp at h

-- LLM HELPER
lemma foldl_single {α β : Type*} (f : α → β → α) (init : α) (x : β) : 
  List.foldl f init [x] = f init x := by
  simp [List.foldl]

-- LLM HELPER
lemma string_nonempty_data_nonempty (s : String) (h : s.length ≠ 0) : s.data ≠ [] := by
  intro h_empty
  have : s.length = 0 := by
    rw [← String.length_data, h_empty]
    simp
  contradiction

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
      have h_empty : s.data = [] := empty_string_data_empty s h
      simp [h_empty]
    · by_cases h1 : s.length = 1
      · -- single character case
        simp [h, h1]
        have h_data_len : s.data.length = 1 := by
          rw [String.length_data]
          exact h1
        obtain ⟨c, hc⟩ := single_char_list s.data h_data_len
        rw [hc]
        simp [foldl_single]
      · -- multi character case
        simp [h, h1]
        have h_nonempty : s.data ≠ [] := string_nonempty_data_nonempty s h
        cases s.data with
        | nil => contradiction
        | cons c rest => 
          simp [List.foldl]
          congr 1
          simp [implementation, String.drop, String.data_drop]

-- #test implementation "" = 0
-- #test implementation "abAB" = 131
-- #test implementation "abcCd" = 67
-- #test implementation "helloE" = 69
-- #test implementation "woArBld" = 131
-- #test implementation "aAaaaXa" = 153
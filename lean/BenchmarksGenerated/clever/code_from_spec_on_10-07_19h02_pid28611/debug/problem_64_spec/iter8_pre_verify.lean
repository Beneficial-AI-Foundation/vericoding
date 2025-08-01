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
let isVowel (c : Char) :=
  let vowels := "aeiouAEIOU"
  vowels.contains c
let isY (c : Char) := c = 'y' ∨ c = 'Y'
-- spec
let spec (result: Nat) :=
string.data.all (fun c => c.isAlpha) →
if string.length = 1 then
  result = if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
else
  result = (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def isVowel (c : Char) : Bool :=
  let vowels := "aeiouAEIOU"
  vowels.contains c

-- LLM HELPER
def isY (c : Char) : Bool := c = 'y' ∨ c = 'Y'

-- LLM HELPER
lemma string_drop_length_lt (s : String) (h : s.length > 0) : (s.drop 1).length < s.length := by
  rw [String.length, String.drop]
  simp only [List.length]
  cases s.data with
  | nil => 
    simp at h
    exact False.elim h
  | cons head tail => 
    simp only [List.length]
    omega

-- LLM HELPER
lemma decide_bool_eq (b : Bool) : decide (b = true) = true ↔ b = true := by
  cases b <;> simp

def implementation (string: String) : Nat := 
  if string.length = 1 then
    if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
  else if string.length = 0 then 0
  else
    (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1)
termination_by string.length
decreasing_by
  apply string_drop_length_lt
  omega

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    by_cases h : s.length = 1
    · simp [h, implementation]
      unfold isVowel isY
      simp only [Bool.decide_coe]
      congr 1
      rw [decide_bool_eq]
    · simp [h, implementation]
      by_cases h_empty : s.length = 0
      · simp [h_empty]
        rfl
      · simp [h_empty]
        rfl
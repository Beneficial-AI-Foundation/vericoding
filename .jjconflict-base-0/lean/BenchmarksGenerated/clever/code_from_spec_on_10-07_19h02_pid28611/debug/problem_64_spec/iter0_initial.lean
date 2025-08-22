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

def implementation (string: String) : Nat := 
  if string.length = 1 then
    if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
  else if string.length = 0 then 0
  else
    (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1)

-- LLM HELPER
lemma drop_length_lt (s : String) (h : s.length > 0) : (s.drop 1).length < s.length := by
  simp [String.length_drop]
  omega

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    simp [isVowel, isY]
    by_cases h : s.length = 1
    · simp [h, implementation]
    · simp [h]
      by_cases h_empty : s.length = 0
      · simp [h_empty, implementation]
      · simp [implementation]
        push_neg at h
        have h_pos : s.length > 0 := Nat.pos_of_ne_zero h_empty
        have h_ge_one : s.length ≥ 1 := h_pos
        have h_not_one : s.length ≠ 1 := h
        have h_gt_one : s.length > 1 := Nat.lt_of_le_of_ne h_ge_one h_not_one.symm
        simp [Nat.not_eq_zero_of_zero_lt h_gt_one]
        simp [if_neg h_not_one]
        rfl
termination_by s.length
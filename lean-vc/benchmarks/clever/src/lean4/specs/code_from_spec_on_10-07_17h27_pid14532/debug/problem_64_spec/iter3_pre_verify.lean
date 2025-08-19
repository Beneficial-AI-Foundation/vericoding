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

def implementation (string: String) : Nat := 
  if string.length = 0 then 0
  else if string.length = 1 then
    let c := string.data[0]!
    let isVowel (c : Char) :=
      let vowels := "aeiouAEIOU"
      vowels.contains c
    let isY (c : Char) := c = 'y' ∨ c = 'Y'
    if isVowel c ∨ isY c then 1 else 0
  else
    let c := string.data[0]!
    let isVowel (c : Char) :=
      let vowels := "aeiouAEIOU"
      vowels.contains c
    (if isVowel c then 1 else 0) + implementation (string.drop 1)
termination_by string.length
decreasing_by
  simp_wf
  have h : string.length ≠ 0 := by simp at *; assumption
  have h2 : string.length ≠ 1 := by simp at *; assumption
  have : string.length > 1 := by
    cases' Nat.lt_or_ge string.length 2 with h3 h3
    · interval_cases string.length
      · contradiction
      · contradiction
    · exact h3
  have : string.drop 1 |>.length < string.length := by
    rw [String.length_drop]
    simp only [tsub_lt_iff_left]
    exact Nat.one_pos

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  simp only [exists_prop]
  use implementation s
  constructor
  · rfl
  · intro h
    simp only [implementation]
    split_ifs with h1 h2
    · simp [String.length_eq_zero] at h1
      rw [h1]
      simp [String.data_empty]
    · rfl
    · rfl
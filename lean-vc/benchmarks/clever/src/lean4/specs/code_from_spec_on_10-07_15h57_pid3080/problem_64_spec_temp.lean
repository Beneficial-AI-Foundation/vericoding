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
  vowels.any (· = c)
let isY (c : Char) := c = 'y' ∨ c = 'Y'
-- spec
let spec (result: Nat) :=
string.toList.all (fun c => c.isAlpha) →
if string.length = 1 then
  result = if isVowel string.toList[0]! ∨ isY string.toList[0]! then 1 else 0
else
  result = (if isVowel string.toList[0]! then 1 else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

def implementation (string: String) : Nat := 
  if string.length = 0 then 0
  else if string.length = 1 then
    let c := string.toList[0]!
    let isVowel (c : Char) :=
      let vowels := "aeiouAEIOU"
      vowels.any (· = c)
    let isY (c : Char) := c = 'y' ∨ c = 'Y'
    if isVowel c ∨ isY c then 1 else 0
  else
    let c := string.toList[0]!
    let isVowel (c : Char) :=
      let vowels := "aeiouAEIOU"
      vowels.any (· = c)
    (if isVowel c then 1 else 0) + implementation (string.drop 1)

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  let isVowel (c : Char) :=
    let vowels := "aeiouAEIOU"
    vowels.any (· = c)
  let isY (c : Char) := c = 'y' ∨ c = 'Y'
  let spec (result: Nat) :=
    s.toList.all (fun c => c.isAlpha) →
    if s.length = 1 then
      result = if isVowel s.toList[0]! ∨ isY s.toList[0]! then 1 else 0
    else
      result = (if isVowel s.toList[0]! then 1 else 0) + implementation (s.drop 1)
  
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    unfold implementation
    by_cases h : s.length = 0
    · simp [h]
      by_cases h1 : s.length = 1
      · simp at h1
        rw [h] at h1
        simp at h1
      · simp [h1]
        simp [h]
    · by_cases h1 : s.length = 1
      · simp [h1]
        simp [h]
      · simp [h1]
        simp [h]
        by_cases h2 : s.length = 1
        · contradiction
        · simp [h2]
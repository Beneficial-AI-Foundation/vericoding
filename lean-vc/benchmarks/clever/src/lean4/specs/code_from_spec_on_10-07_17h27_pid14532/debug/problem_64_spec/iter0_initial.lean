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

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  simp only [exists_prop]
  constructor
  · rfl
  · intro h
    simp only [implementation]
    split_ifs with h1 h2
    · rfl
    · rfl
    · rfl
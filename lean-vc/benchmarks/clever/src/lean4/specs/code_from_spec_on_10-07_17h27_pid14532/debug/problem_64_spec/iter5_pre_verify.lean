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
lemma string_drop_length (s : String) : s.length > 0 → (s.drop 1).length = s.length - 1 := by
  intro h
  rw [String.length_drop]
  simp [Nat.succ_sub_succ_eq_sub]

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
  have h_pos : string.length > 0 := by
    by_contra h
    simp at h
    contradiction
  have h_gt_one : string.length > 1 := by
    by_contra h
    simp at h
    cases' Nat.lt_or_eq_of_le h with h' h'
    · simp at h'
      contradiction
    · contradiction
  rw [string_drop_length string h_pos]
  exact Nat.sub_lt h_pos (by norm_num)

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
    unfold implementation
    split_ifs with h1 h2
    · simp [String.length_eq_zero] at h1
      rw [h1]
      simp [String.data_empty]
    · rfl
    · rfl
import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s: String) :=
-- spec
let spec (result : String) :=
  s.data.all (λ c => c.isAlpha) →
  result.length = s.length ∧
  (∀ i, i < s.length →
    let c := s.data.get! i;
    let c' := result.data.get! i;
    match c with
    | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' =>
      c.isUpper → c'.val = c.toLower.val + 2 ∧
      c.isLower → c'.val = c.toUpper.val + 2
    | _ =>
      c.isUpper → c' = c.toLower ∧
      c.isLower → c' = c.toUpper)
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
def isVowel (c : Char) : Bool :=
  c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u' ||
  c = 'A' || c = 'E' || c = 'I' || c = 'O' || c = 'U'

-- LLM HELPER
def transformChar (c : Char) : Char :=
  if isVowel c then
    if c.isUpper then
      Char.ofNat (c.toLower.val + 2)
    else
      Char.ofNat (c.toUpper.val + 2)
  else
    if c.isUpper then
      c.toLower
    else
      c.toUpper

def implementation (s: String) : String := 
  String.mk (s.data.map transformChar)

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use String.mk (s.data.map transformChar)
  constructor
  · rfl
  · intro h
    constructor
    · simp [implementation, String.length]
      rw [String.length_mk, List.length_map]
      rfl
    · intro i hi
      simp [implementation]
      have h1 : i < s.data.length := by
        rw [← String.length_data] at hi
        exact hi
      simp [String.get!_eq, List.get!_eq_get, h1]
      let c := s.data.get! i
      let c' := (s.data.map transformChar).get! i
      have h2 : c' = transformChar c := by
        simp [List.get!_eq_get, List.get_map, h1]
      rw [h2]
      unfold transformChar
      -- Case analysis on vowels
      by_cases hv : isVowel c
      · -- c is a vowel
        simp [hv]
        unfold isVowel at hv
        simp at hv
        -- vowel case with upper/lower handling
        split_ifs with h_upper h_lower
        · -- c is upper vowel
          simp [h_upper]
          simp [Char.isUpper] at h_upper
          simp [h_upper]
        · -- c is lower vowel  
          simp [h_lower]
          simp [Char.isLower] at h_lower
          simp [h_lower]
      · -- c is not a vowel
        simp [hv]
        split_ifs with h_upper h_lower
        · -- c is upper consonant
          simp [h_upper]
          simp [Char.isUpper] at h_upper
          simp [h_upper]
        · -- c is lower consonant
          simp [h_lower]
          simp [Char.isLower] at h_lower
          simp [h_lower]
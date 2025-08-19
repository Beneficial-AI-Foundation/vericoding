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
def is_vowel (c : Char) : Bool :=
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' => true
  | _ => false

-- LLM HELPER
def transform_char (c : Char) : Char :=
  if is_vowel c then
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
  String.mk (s.data.map transform_char)

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec, implementation]
  use String.mk (s.data.map transform_char)
  constructor
  · rfl
  · intro h
    constructor
    · simp [String.length, String.mk]
    · intro i hi
      simp [String.data, String.mk]
      have h_get : (s.data.map transform_char).get! i = transform_char (s.data.get! i) := by
        rw [List.get!_map]
      rw [h_get]
      simp [transform_char, is_vowel]
      by_cases h_vowel : match s.data.get! i with
        | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' => true
        | _ => false
      · simp [h_vowel]
        by_cases h_upper : (s.data.get! i).isUpper
        · simp [h_upper]
          constructor
          · intro
            rfl
          · intro h_lower
            have : ¬(s.data.get! i).isLower := by
              simp [Char.isLower, Char.isUpper] at h_upper h_lower
              exact Char.not_isLower_of_isUpper h_upper
            contradiction
        · simp [h_upper]
          constructor
          · intro h_upper_false
            contradiction
          · intro
            rfl
      · simp [h_vowel]
        by_cases h_upper : (s.data.get! i).isUpper
        · simp [h_upper]
          constructor
          · intro
            rfl
          · intro h_lower
            have : ¬(s.data.get! i).isLower := by
              simp [Char.isLower, Char.isUpper] at h_upper h_lower
              exact Char.not_isLower_of_isUpper h_upper
            contradiction
        · simp [h_upper]
          constructor
          · intro h_upper_false
            contradiction
          · intro
            rfl
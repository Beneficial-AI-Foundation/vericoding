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
  match c with
  | 'a' | 'e' | 'i' | 'o' | 'u' | 'A' | 'E' | 'I' | 'O' | 'U' => true
  | _ => false

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
    · simp [implementation, String.length, List.length_map]
    · intro i hi
      simp [implementation, String.mk]
      simp [List.get!_map]
      unfold transformChar
      simp [isVowel]
      cases' c : s.data.get! i with val
      split_ifs with h1 h2 h3
      · simp [h1, h2, h3]
        split
        · simp [Char.isUpper, Char.val_ofNat]
        · simp [Char.isLower, Char.val_ofNat]
      · simp [h1, h2]
        split
        · simp [Char.isUpper]
        · simp [Char.isLower]
      · simp [h1]
        split
        · simp [Char.isUpper]
        · simp [Char.isLower]
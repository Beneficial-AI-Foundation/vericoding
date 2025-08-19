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
(s : String) :=
let isAlphabetic (string: String) : Bool :=
∀ i, i < string.length →
let c := string.get! ⟨i⟩;
('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)
-- spec
let spec (result: String) :=
isAlphabetic result ∧ isAlphabetic s ∧
result.length = s.length ∧
∃ k : Nat, k < 26 ∧
∀ i : Nat, i < s.length →
((s.get! ⟨i⟩).toNat + k) % 26 = (result.get! ⟨i⟩).toNat
→ k = 5
-- program termination
∃ result, implementation s = result ∧
spec result

-- LLM HELPER
def shiftChar (c : Char) (k : Nat) : Char :=
if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat then
  Char.ofNat (('a'.toNat + ((c.toNat - 'a'.toNat) + k) % 26))
else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat then
  Char.ofNat (('A'.toNat + ((c.toNat - 'A'.toNat) + k) % 26))
else
  c

-- LLM HELPER  
def shiftString (s : String) (k : Nat) : String :=
s.map (fun c => shiftChar c k)

def implementation (s: String) : String := shiftString s 5

-- LLM HELPER
lemma isAlphabetic_preserved (s : String) (k : Nat) :
  (∀ i, i < s.length →
    let c := s.get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (∀ i, i < (shiftString s k).length →
    let c := (shiftString s k).get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) :=
by
  intro h i hi
  simp [shiftString, String.map] at hi ⊢
  rw [String.get!_map]
  simp [shiftChar]
  have h_orig := h i hi
  let c := s.get! ⟨i⟩
  by_cases hc : 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat
  · simp [hc]
    left
    simp [Char.ofNat]
    constructor
    · sorry
    · sorry
  · by_cases hc2 : 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat
    · simp [hc, hc2]
      right
      simp [Char.ofNat]
      constructor
      · sorry
      · sorry
    · simp [hc, hc2]
      cases' h_orig with h_lower h_upper
      · exact False.elim (hc h_lower)
      · exact False.elim (hc2 h_upper)

-- LLM HELPER
lemma length_preserved (s : String) (k : Nat) :
  (shiftString s k).length = s.length :=
by
  simp [shiftString]
  rw [String.map_length]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec implementation
  simp
  use shiftString s 5
  constructor
  · rfl
  · simp
    constructor
    · -- isAlphabetic (shiftString s 5)
      apply isAlphabetic_preserved
      sorry
    · constructor
      · -- isAlphabetic s
        sorry
      · constructor
        · -- length preservation
          exact length_preserved s 5
        · -- existence of k = 5
          use 5
          constructor
          · norm_num
          · intro i hi
            intro h
            simp [shiftString, String.map] at h
            rw [String.get!_map] at h
            simp [shiftChar] at h
            sorry
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
  Char.ofNat (('a'.toNat + (c.toNat - 'a'.toNat + k) % 26))
else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat then
  Char.ofNat (('A'.toNat + (c.toNat - 'A'.toNat + k) % 26))
else
  c

-- LLM HELPER
def shiftString (s : String) (k : Nat) : String :=
String.mk (s.data.map (fun c => shiftChar c k))

def implementation (s: String) : String := shiftString s 5

-- LLM HELPER
lemma shiftChar_preserves_alphabetic (c : Char) (k : Nat) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (('a'.toNat ≤ (shiftChar c k).toNat ∧ (shiftChar c k).toNat ≤ 'z'.toNat) ∨ 
   ('A'.toNat ≤ (shiftChar c k).toNat ∧ (shiftChar c k).toNat ≤ 'Z'.toNat)) := by
  intro h
  unfold shiftChar
  cases' h with h1 h2
  · simp [h1]
    constructor
    · rw [Char.toNat_ofNat]
      exact Nat.le_add_right _ _
    · rw [Char.toNat_ofNat]
      have : (c.toNat - 'a'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      linarith
  · simp [h2]
    right
    constructor
    · rw [Char.toNat_ofNat]
      exact Nat.le_add_right _ _
    · rw [Char.toNat_ofNat]
      have : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      linarith

-- LLM HELPER
lemma shiftString_preserves_alphabetic (s : String) (k : Nat) :
  (∀ i, i < s.length → 
    let c := s.get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (∀ i, i < (shiftString s k).length → 
    let c := (shiftString s k).get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) := by
  intro h i hi
  unfold shiftString at hi ⊢
  simp at hi ⊢
  have : i < s.length := by
    rw [String.length_mk] at hi
    rw [List.length_map] at hi
    exact hi
  specialize h i this
  have : (String.mk (s.data.map (fun c => shiftChar c k))).get! ⟨i⟩ = shiftChar (s.get! ⟨i⟩) k := by
    rw [String.get!_mk]
    simp
    rw [List.get_map]
    simp
  rw [this]
  exact shiftChar_preserves_alphabetic (s.get! ⟨i⟩) k h

-- LLM HELPER
lemma shiftString_length (s : String) (k : Nat) :
  (shiftString s k).length = s.length := by
  unfold shiftString
  rw [String.length_mk]
  rw [List.length_map]

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec implementation
  simp
  use shiftString s 5
  constructor
  · rfl
  · constructor
    · exact shiftString_preserves_alphabetic s 5
    · constructor
      · intro h
        exact h
      · constructor
        · exact shiftString_length s 5
        · use 5
          constructor
          · norm_num
          · intro h
            exact fun _ => rfl
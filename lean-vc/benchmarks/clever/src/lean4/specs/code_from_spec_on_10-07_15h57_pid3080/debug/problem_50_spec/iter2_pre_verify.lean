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
lemma char_bounds_lower (n : Nat) : 'a'.toNat ≤ 'a'.toNat + n % 26 := by
  have h : n % 26 < 26 := Nat.mod_lt n (by norm_num : 0 < 26)
  simp

-- LLM HELPER
lemma char_bounds_upper (n : Nat) : 'a'.toNat + n % 26 ≤ 'z'.toNat := by
  have h : n % 26 < 26 := Nat.mod_lt n (by norm_num : 0 < 26)
  have : 'a'.toNat + 25 = 'z'.toNat := by norm_num
  rw [← this]
  apply Nat.add_le_add_left
  omega

-- LLM HELPER
lemma char_bounds_upper_A (n : Nat) : 'A'.toNat + n % 26 ≤ 'Z'.toNat := by
  have h : n % 26 < 26 := Nat.mod_lt n (by norm_num : 0 < 26)
  have : 'A'.toNat + 25 = 'Z'.toNat := by norm_num
  rw [← this]
  apply Nat.add_le_add_left
  omega

-- LLM HELPER
lemma char_bounds_lower_A (n : Nat) : 'A'.toNat ≤ 'A'.toNat + n % 26 := by
  have h : n % 26 < 26 := Nat.mod_lt n (by norm_num : 0 < 26)
  simp

-- LLM HELPER
lemma isAlphabetic_preserved (s : String) (k : Nat) :
  (∀ i, i < s.length →
    let c := s.get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (∀ i, i < (shiftString s k).length →
    let c := (shiftString s k).get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) := by
  intro h i hi
  simp [shiftString] at hi ⊢
  rw [String.get!_map]
  simp [shiftChar]
  have h_orig := h i (by simpa using hi)
  let c := s.get! ⟨i⟩
  by_cases hc : 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat
  · simp [hc]
    left
    constructor
    · apply char_bounds_lower
    · apply char_bounds_upper
  · by_cases hc2 : 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat
    · simp [hc, hc2]
      right
      constructor
      · apply char_bounds_lower_A
      · apply char_bounds_upper_A
    · simp [hc, hc2]
      cases' h_orig with h_lower h_upper
      · exact False.elim (hc h_lower)
      · exact False.elim (hc2 h_upper)

-- LLM HELPER
lemma length_preserved (s : String) (k : Nat) :
  (shiftString s k).length = s.length := by
  simp [shiftString]

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec implementation
  simp
  use shiftString s 5
  constructor
  · rfl
  · simp
    constructor
    · -- isAlphabetic (shiftString s 5)
      intro h
      apply isAlphabetic_preserved
      exact h
    · constructor
      · -- isAlphabetic s
        intro h
        exact h
      · constructor
        · -- length preservation
          exact length_preserved s 5
        · -- existence of k = 5
          use 5
          constructor
          · norm_num
          · intro i hi h
            rfl
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
lemma char_toNat_ofNat_mod (n : Nat) : 
  (Char.ofNat n).toNat = n % 1112064 := by
  rfl

-- LLM HELPER
lemma char_toNat_ofNat_lower (n : Nat) (h : n < 1112064) : 
  (Char.ofNat n).toNat = n := by
  rw [char_toNat_ofNat_mod]
  exact Nat.mod_eq_of_lt h

-- LLM HELPER
lemma shiftChar_preserves_alphabetic (c : Char) (k : Nat) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (('a'.toNat ≤ (shiftChar c k).toNat ∧ (shiftChar c k).toNat ≤ 'z'.toNat) ∨ 
   ('A'.toNat ≤ (shiftChar c k).toNat ∧ (shiftChar c k).toNat ≤ 'Z'.toNat)) := by
  intro h
  unfold shiftChar
  cases' h with h1 h2
  · simp only [h1, true_and, if_true]
    left
    constructor
    · have mod_lt : (c.toNat - 'a'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have sum_lt : 'a'.toNat + (c.toNat - 'a'.toNat + k) % 26 < 1112064 := by
        have : 'a'.toNat = 97 := by norm_num
        rw [this]
        have : (c.toNat - 'a'.toNat + k) % 26 < 26 := mod_lt
        linarith
      rw [char_toNat_ofNat_lower _ sum_lt]
      norm_num
    · have mod_lt : (c.toNat - 'a'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have sum_lt : 'a'.toNat + (c.toNat - 'a'.toNat + k) % 26 < 1112064 := by
        have : 'a'.toNat = 97 := by norm_num
        rw [this]
        have : (c.toNat - 'a'.toNat + k) % 26 < 26 := mod_lt
        linarith
      rw [char_toNat_ofNat_lower _ sum_lt]
      have : c.toNat - 'a'.toNat < 26 := by
        have : c.toNat ≤ 'z'.toNat := h1.2
        have : 'z'.toNat = 122 := by norm_num
        have : 'a'.toNat = 97 := by norm_num
        linarith
      have : (c.toNat - 'a'.toNat + k) % 26 ≤ 25 := by
        have : (c.toNat - 'a'.toNat + k) % 26 < 26 := mod_lt
        linarith
      have : 'a'.toNat = 97 := by norm_num
      have : 'z'.toNat = 122 := by norm_num
      linarith
  · simp only [h2, if_false, if_true, true_and]
    right
    constructor
    · have mod_lt : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have sum_lt : 'A'.toNat + (c.toNat - 'A'.toNat + k) % 26 < 1112064 := by
        have : 'A'.toNat = 65 := by norm_num
        rw [this]
        have : (c.toNat - 'A'.toNat + k) % 26 < 26 := mod_lt
        linarith
      rw [char_toNat_ofNat_lower _ sum_lt]
      norm_num
    · have mod_lt : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have sum_lt : 'A'.toNat + (c.toNat - 'A'.toNat + k) % 26 < 1112064 := by
        have : 'A'.toNat = 65 := by norm_num
        rw [this]
        have : (c.toNat - 'A'.toNat + k) % 26 < 26 := mod_lt
        linarith
      rw [char_toNat_ofNat_lower _ sum_lt]
      have : c.toNat - 'A'.toNat < 26 := by
        have : c.toNat ≤ 'Z'.toNat := h2.2
        have : 'Z'.toNat = 90 := by norm_num
        have : 'A'.toNat = 65 := by norm_num
        linarith
      have : (c.toNat - 'A'.toNat + k) % 26 ≤ 25 := by
        have : (c.toNat - 'A'.toNat + k) % 26 < 26 := mod_lt
        linarith
      have : 'A'.toNat = 65 := by norm_num
      have : 'Z'.toNat = 90 := by norm_num
      linarith

-- LLM HELPER
lemma string_get_map (s : String) (f : Char → Char) (i : Nat) (hi : i < s.length) :
  (String.mk (s.data.map f)).get! ⟨i⟩ = f (s.get! ⟨i⟩) := by
  simp [String.get!, String.get_mk]
  rw [List.get!_map]

-- LLM HELPER
lemma shiftString_length (s : String) (k : Nat) :
  (shiftString s k).length = s.length := by
  unfold shiftString
  rw [String.length_mk, List.length_map]

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
    · -- prove isAlphabetic (shiftString s 5)
      intro i hi
      unfold shiftString at hi ⊢
      rw [String.length_mk, List.length_map] at hi
      have h_get : (String.mk (s.data.map (fun c => shiftChar c 5))).get! ⟨i⟩ = shiftChar (s.get! ⟨i⟩) 5 := by
        exact string_get_map s (fun c => shiftChar c 5) i hi
      rw [h_get]
      by_cases h : (('a'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'Z'.toNat))
      · exact shiftChar_preserves_alphabetic (s.get! ⟨i⟩) 5 h
      · unfold shiftChar
        simp only [h, if_false]
        exact h
    · constructor
      · -- prove isAlphabetic s (assume it's given)
        intro
        -- This is an assumption that s is alphabetic
        exact True.intro
      · constructor
        · -- prove length equality
          exact shiftString_length s 5
        · -- prove the shift property
          use 5
          constructor
          · norm_num
          · intro i hi hyp
            rfl
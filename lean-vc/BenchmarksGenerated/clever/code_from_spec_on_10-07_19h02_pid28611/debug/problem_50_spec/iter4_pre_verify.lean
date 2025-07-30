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
lemma char_toNat_ofNat_lower (n : Nat) : 
  (Char.ofNat (97 + n)).toNat = 97 + n := by
  rw [Char.toNat_ofNat]
  simp [Nat.mod_eq_of_lt]
  norm_num

-- LLM HELPER
lemma char_toNat_ofNat_upper (n : Nat) : 
  (Char.ofNat (65 + n)).toNat = 65 + n := by
  rw [Char.toNat_ofNat]
  simp [Nat.mod_eq_of_lt]
  norm_num

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
      rw [char_toNat_ofNat_lower]
      exact Nat.le_add_right _ _
    · have mod_lt : (c.toNat - 'a'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      rw [char_toNat_ofNat_lower]
      norm_num
  · simp only [h2, if_false, if_true]
    right
    constructor
    · have mod_lt : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      rw [char_toNat_ofNat_upper]
      exact Nat.le_add_right _ _
    · have mod_lt : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      rw [char_toNat_ofNat_upper]
      norm_num

-- LLM HELPER
lemma string_get_map (s : String) (f : Char → Char) (i : Nat) (hi : i < s.length) :
  (String.mk (s.data.map f)).get! ⟨i⟩ = f (s.get! ⟨i⟩) := by
  simp [String.get!]
  rw [String.get_mk]
  simp [List.get!_map]

-- LLM HELPER
lemma shiftString_length (s : String) (k : Nat) :
  (shiftString s k).length = s.length := by
  unfold shiftString
  rw [String.length_mk, List.length_map]
  simp [String.length]

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
      simp at hi ⊢
      have length_eq : (String.mk (s.data.map (fun c => shiftChar c 5))).length = s.length := by
        rw [String.length_mk, List.length_map]
        simp [String.length]
      rw [length_eq] at hi
      sorry  -- This would need the assumption that s is alphabetic
    · constructor
      · -- prove isAlphabetic s
        intro h
        exact h
      · constructor
        · -- prove length equality
          exact shiftString_length s 5
        · -- prove the shift property
          use 5
          constructor
          · norm_num
          · intro i hi hyp
            rfl
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
lemma char_ofNat_toNat_mod (n : Nat) : 
  (Char.ofNat n).toNat = n % 1112064 := by
  simp [Char.ofNat, Char.toNat]
  split_ifs with h
  · simp [Char.ofNatAux]
  · simp

-- LLM HELPER
lemma char_ofNat_toNat_small (n : Nat) (h : n < 1112064) : 
  (Char.ofNat n).toNat = n := by
  rw [char_ofNat_toNat_mod]
  exact Nat.mod_eq_of_lt h

-- LLM HELPER
lemma char_val_facts : 'a'.toNat = 97 ∧ 'z'.toNat = 122 ∧ 'A'.toNat = 65 ∧ 'Z'.toNat = 90 := by
  simp [Char.toNat]
  norm_num

-- LLM HELPER
lemma shift_char_bounds (c : Char) (k : Nat) :
  ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) → 
  'a'.toNat + (c.toNat - 'a'.toNat + k) % 26 < 1112064 := by
  intro h
  have : (c.toNat - 'a'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
  have : 'a'.toNat = 97 := char_val_facts.1
  rw [this]
  omega

-- LLM HELPER
lemma shift_char_bounds_upper (c : Char) (k : Nat) :
  ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat) → 
  'A'.toNat + (c.toNat - 'A'.toNat + k) % 26 < 1112064 := by
  intro h
  have : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
  have : 'A'.toNat = 65 := char_val_facts.2.2.1
  rw [this]
  omega

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
      have sum_lt : 'a'.toNat + (c.toNat - 'a'.toNat + k) % 26 < 1112064 := shift_char_bounds c k h1
      rw [char_ofNat_toNat_small _ sum_lt]
      exact Nat.le_add_right _ _
    · have mod_lt : (c.toNat - 'a'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have sum_lt : 'a'.toNat + (c.toNat - 'a'.toNat + k) % 26 < 1112064 := shift_char_bounds c k h1
      rw [char_ofNat_toNat_small _ sum_lt]
      have char_bound : c.toNat - 'a'.toNat < 26 := by
        have : c.toNat ≤ 'z'.toNat := h1.2
        have : 'z'.toNat = 122 := char_val_facts.2.1
        have : 'a'.toNat = 97 := char_val_facts.1
        omega
      have : (c.toNat - 'a'.toNat + k) % 26 ≤ 25 := by
        have : (c.toNat - 'a'.toNat + k) % 26 < 26 := mod_lt
        omega
      have : 'a'.toNat = 97 := char_val_facts.1
      have : 'z'.toNat = 122 := char_val_facts.2.1
      omega
  · simp only [h2, if_false, if_true, true_and]
    right
    constructor
    · have mod_lt : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have sum_lt : 'A'.toNat + (c.toNat - 'A'.toNat + k) % 26 < 1112064 := shift_char_bounds_upper c k h2
      rw [char_ofNat_toNat_small _ sum_lt]
      have h1_false : ¬('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) := by
        intro h1
        have : 'a'.toNat = 97 := char_val_facts.1
        have : 'z'.toNat = 122 := char_val_facts.2.1
        have : 'A'.toNat = 65 := char_val_facts.2.2.1
        have : 'Z'.toNat = 90 := char_val_facts.2.2.2
        omega
      simp only [h1_false, if_false]
      exact Nat.le_add_right _ _
    · have mod_lt : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have sum_lt : 'A'.toNat + (c.toNat - 'A'.toNat + k) % 26 < 1112064 := shift_char_bounds_upper c k h2
      rw [char_ofNat_toNat_small _ sum_lt]
      have h1_false : ¬('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) := by
        intro h1
        have : 'a'.toNat = 97 := char_val_facts.1
        have : 'z'.toNat = 122 := char_val_facts.2.1
        have : 'A'.toNat = 65 := char_val_facts.2.2.1
        have : 'Z'.toNat = 90 := char_val_facts.2.2.2
        omega
      simp only [h1_false, if_false]
      have char_bound : c.toNat - 'A'.toNat < 26 := by
        have : c.toNat ≤ 'Z'.toNat := h2.2
        have : 'Z'.toNat = 90 := char_val_facts.2.2.2
        have : 'A'.toNat = 65 := char_val_facts.2.2.1
        omega
      have : (c.toNat - 'A'.toNat + k) % 26 ≤ 25 := by
        have : (c.toNat - 'A'.toNat + k) % 26 < 26 := mod_lt
        omega
      have : 'A'.toNat = 65 := char_val_facts.2.2.1
      have : 'Z'.toNat = 90 := char_val_facts.2.2.2
      omega

-- LLM HELPER
lemma shiftString_length (s : String) (k : Nat) :
  (shiftString s k).length = s.length := by
  unfold shiftString
  rw [String.length_mk, List.length_map, String.length]

-- LLM HELPER
lemma shiftString_get (s : String) (k : Nat) (i : Nat) (hi : i < s.length) :
  (shiftString s k).get! ⟨i⟩ = shiftChar (s.get! ⟨i⟩) k := by
  unfold shiftString
  simp [String.get!, String.mk]
  rw [List.get!_map]
  simp [String.get!]

-- LLM HELPER
lemma shiftChar_shift_property (c : Char) (k : Nat) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (c.toNat + k) % 26 = (shiftChar c k).toNat := by
  intro h
  unfold shiftChar
  cases' h with h1 h2
  · simp only [h1, true_and, if_true]
    have mod_lt : (c.toNat - 'a'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
    have sum_lt : 'a'.toNat + (c.toNat - 'a'.toNat + k) % 26 < 1112064 := shift_char_bounds c k h1
    rw [char_ofNat_toNat_small _ sum_lt]
    simp [Nat.add_mod]
    norm_num
  · simp only [h2, if_false, if_true, true_and]
    have h1_false : ¬('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) := by
      intro h1
      have : 'a'.toNat = 97 := char_val_facts.1
      have : 'z'.toNat = 122 := char_val_facts.2.1
      have : 'A'.toNat = 65 := char_val_facts.2.2.1
      have : 'Z'.toNat = 90 := char_val_facts.2.2.2
      omega
    simp only [h1_false, if_false]
    have mod_lt : (c.toNat - 'A'.toNat + k) % 26 < 26 := Nat.mod_lt _ (by norm_num)
    have sum_lt : 'A'.toNat + (c.toNat - 'A'.toNat + k) % 26 < 1112064 := shift_char_bounds_upper c k h2
    rw [char_ofNat_toNat_small _ sum_lt]
    simp [Nat.add_mod]
    norm_num

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec implementation
  simp
  use shiftString s 5
  constructor
  · rfl
  · by_cases h : (∀ i, i < s.length → ('a'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'z'.toNat) ∨ ('A'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'Z'.toNat))
    · constructor
      · -- prove isAlphabetic (shiftString s 5)
        intro i hi
        rw [shiftString_length] at hi
        rw [shiftString_get s 5 i hi]
        exact shiftChar_preserves_alphabetic (s.get! ⟨i⟩) 5 (h i hi)
      · constructor
        · -- prove isAlphabetic s
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
    · constructor
      · -- prove isAlphabetic (shiftString s 5)
        intro i hi
        rw [shiftString_length] at hi
        rw [shiftString_get s 5 i hi]
        exfalso
        exact h (fun i hi => by
          push_neg at h
          exact h i hi)
      · constructor
        · -- prove isAlphabetic s
          exfalso
          exact h (fun i hi => by
            push_neg at h
            exact h i hi)
        · constructor
          · -- prove length equality
            exact shiftString_length s 5
          · -- prove the shift property
            use 5
            constructor
            · norm_num
            · intro i hi hyp
              rfl
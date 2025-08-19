import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def isAlphabetic (string: String) : Bool :=
string.all (fun c => 
  ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
  ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat))

def problem_spec
-- function signature
(implementation: String → String)
-- inputs
(s : String) :=
-- spec
let spec (result: String) :=
isAlphabetic result = true ∧ isAlphabetic s = true ∧
result.length = s.length ∧
∃ k : Nat, k < 26 ∧
∀ i : Nat, i < s.length →
((s.get! ⟨i⟩).toNat + k) % 26 = (result.get! ⟨i⟩).toNat
→ k = 5
-- program termination
∃ result, implementation s = result ∧
spec result

-- LLM HELPER
def shift_char (c: Char) (k: Nat) : Char :=
if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat then
  Char.ofNat (('a'.toNat + (c.toNat - 'a'.toNat + k) % 26))
else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat then
  Char.ofNat (('A'.toNat + (c.toNat - 'A'.toNat + k) % 26))
else c

-- LLM HELPER
def caesar_cipher (s: String) (k: Nat) : String :=
s.map (fun c => shift_char c k)

def implementation (s: String) : String := caesar_cipher s 5

-- LLM HELPER
lemma shift_char_preserves_alphabetic (c: Char) (k: Nat) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
   ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (('a'.toNat ≤ (shift_char c k).toNat ∧ (shift_char c k).toNat ≤ 'z'.toNat) ∨
   ('A'.toNat ≤ (shift_char c k).toNat ∧ (shift_char c k).toNat ≤ 'Z'.toNat)) :=
by
  intro h
  simp [shift_char]
  cases' h with h1 h2
  · left
    simp [h1]
    have h_mod := Nat.mod_lt (c.toNat - 'a'.toNat + k) (by norm_num : 26 > 0)
    constructor
    · simp [Char.ofNat, Char.toNat]
      apply Nat.le_add_right
    · simp [Char.ofNat, Char.toNat]
      rw [Nat.add_comm]
      apply Nat.add_le_add_left
      exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt h_mod)
  · right
    simp [h2]
    have h_mod := Nat.mod_lt (c.toNat - 'A'.toNat + k) (by norm_num : 26 > 0)
    constructor
    · simp [Char.ofNat, Char.toNat]
      apply Nat.le_add_right
    · simp [Char.ofNat, Char.toNat]
      rw [Nat.add_comm]
      apply Nat.add_le_add_left
      exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt h_mod)

-- LLM HELPER
lemma caesar_cipher_preserves_length (s: String) (k: Nat) :
  (caesar_cipher s k).length = s.length :=
by
  simp [caesar_cipher]
  rw [String.length_map]

-- LLM HELPER
lemma caesar_cipher_preserves_alphabetic (s: String) (k: Nat) :
  isAlphabetic s = true →
  isAlphabetic (caesar_cipher s k) = true :=
by
  intro h
  simp [isAlphabetic, caesar_cipher]
  rw [String.all_map]
  exact String.all_of_all_map h (fun c => shift_char_preserves_alphabetic c k)

-- LLM HELPER
lemma caesar_cipher_shift_property (s: String) (k: Nat) :
  ∀ i : Nat, i < s.length →
  ((s.get! ⟨i⟩).toNat + k) % 26 = ((caesar_cipher s k).get! ⟨i⟩).toNat :=
by
  intro i hi
  simp [caesar_cipher]
  rw [String.get!_map]
  simp [shift_char]
  split_ifs with h1 h2
  · simp [Char.ofNat, Char.toNat]
    rw [Nat.add_mod, Nat.add_sub_cancel']
    exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Nat.le_of_lt_succ (And.right h1)))
  · simp [Char.ofNat, Char.toNat]
    rw [Nat.add_mod, Nat.add_sub_cancel']
    exact Nat.le_of_lt_succ (Nat.lt_succ_of_lt (Nat.le_of_lt_succ (And.right h2)))
  · simp

theorem correctness
(s: String)
: problem_spec implementation s :=
by
  simp [problem_spec, implementation]
  use caesar_cipher s 5
  constructor
  · rfl
  · simp
    constructor
    · apply caesar_cipher_preserves_alphabetic
      simp
    · constructor
      · simp
      · constructor
        · apply caesar_cipher_preserves_length
        · use 5
          constructor
          · norm_num
          · intro i hi h_eq
            rfl
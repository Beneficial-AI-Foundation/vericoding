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
    constructor
    · sorry
    · sorry
  · right
    simp [h2]
    constructor
    · sorry
    · sorry

-- LLM HELPER
lemma caesar_cipher_preserves_length (s: String) (k: Nat) :
  (caesar_cipher s k).length = s.length :=
by
  simp [caesar_cipher]
  sorry

-- LLM HELPER
lemma caesar_cipher_preserves_alphabetic (s: String) (k: Nat) :
  (∀ i, i < s.length →
    let c := s.get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (∀ i, i < (caesar_cipher s k).length →
    let c := (caesar_cipher s k).get! ⟨i⟩;
    ('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
    ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) :=
by
  intro h i hi
  simp [caesar_cipher] at hi ⊢
  sorry

-- LLM HELPER
lemma caesar_cipher_shift_property (s: String) (k: Nat) :
  ∀ i : Nat, i < s.length →
  ((s.get! ⟨i⟩).toNat + k) % 26 = ((caesar_cipher s k).get! ⟨i⟩).toNat :=
by
  intro i hi
  simp [caesar_cipher, shift_char]
  sorry

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
      sorry
    · constructor
      · sorry
      · constructor
        · apply caesar_cipher_preserves_length
        · use 5
          constructor
          · norm_num
          · intro i hi
            have h := caesar_cipher_shift_property s 5 i hi
            simp at h
            intro h_eq
            sorry
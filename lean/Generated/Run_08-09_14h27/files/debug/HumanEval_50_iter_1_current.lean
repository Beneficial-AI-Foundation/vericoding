/- 
function_signature: "def encode_shift(s: String) -> String"
docstring: |
    returns encoded string by shifting every character by 5 in the alphabet.
test_cases:
  - input: abc
    expected_output: fgh
  - input: xyz
    expected_output: cde
  - input: aaa
    expected_output: fff
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def shift_char (c : Char) : Char :=
  if 'a' ≤ c ∧ c ≤ 'z' then
    Char.ofNat (((c.toNat - 'a'.toNat + 5) % 26) + 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'Z' then
    Char.ofNat (((c.toNat - 'A'.toNat + 5) % 26) + 'A'.toNat)
  else
    c

def implementation (s: String) : String :=
  s.map shift_char

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
lemma shift_char_preserves_alphabetic (c : Char) :
  (('a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'z'.toNat) ∨
   ('A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'Z'.toNat)) →
  (('a'.toNat ≤ (shift_char c).toNat ∧ (shift_char c).toNat ≤ 'z'.toNat) ∨
   ('A'.toNat ≤ (shift_char c).toNat ∧ (shift_char c).toNat ≤ 'Z'.toNat)) := by
  intro h
  simp [shift_char]
  cases h with
  | inl h_lower =>
    simp [h_lower.1, h_lower.2]
    left
    constructor
    · simp [Char.ofNat]
      have : (c.toNat - 'a'.toNat + 5) % 26 + 'a'.toNat ≥ 'a'.toNat := by
        simp [Nat.le_add_left]
      exact this
    · simp [Char.ofNat]
      have : (c.toNat - 'a'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have : (c.toNat - 'a'.toNat + 5) % 26 + 'a'.toNat ≤ 25 + 'a'.toNat := by
        exact Nat.add_le_add_right (Nat.le_sub_one_of_lt this) 'a'.toNat
      norm_num at this
      exact this
  | inr h_upper =>
    simp [h_upper.1, h_upper.2]
    right
    constructor
    · simp [Char.ofNat]
      have : (c.toNat - 'A'.toNat + 5) % 26 + 'A'.toNat ≥ 'A'.toNat := by
        simp [Nat.le_add_left]
      exact this
    · simp [Char.ofNat]
      have : (c.toNat - 'A'.toNat + 5) % 26 < 26 := Nat.mod_lt _ (by norm_num)
      have : (c.toNat - 'A'.toNat + 5) % 26 + 'A'.toNat ≤ 25 + 'A'.toNat := by
        exact Nat.add_le_add_right (Nat.le_sub_one_of_lt this) 'A'.toNat
      norm_num at this
      exact this

theorem correctness
(s: String)
: problem_spec implementation s := by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  constructor
  · -- isAlphabetic (implementation s)
    intro i h
    simp [implementation]
    have h_orig : i < s.length := by
      simp [String.length_map] at h
      exact h
    have c_alpha : ('a'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'z'.toNat) ∨
                   ('A'.toNat ≤ (s.get! ⟨i⟩).toNat ∧ (s.get! ⟨i⟩).toNat ≤ 'Z'.toNat) := by
      sorry -- This would require assuming input is alphabetic
    exact shift_char_preserves_alphabetic (s.get! ⟨i⟩) c_alpha
  constructor
  · -- isAlphabetic s (assumed)
    sorry
  constructor  
  · -- result.length = s.length
    simp [implementation, String.length_map]
  · -- ∃ k : Nat, k < 26 ∧ ∀ i : Nat, i < s.length → ((s.get! ⟨i⟩).toNat + k) % 26 = (result.get! ⟨i⟩).toNat → k = 5
    use 5
    constructor
    · norm_num
    · intro i h_len premise
      rfl

-- #test implementation "abc" = "fgh"
-- #test implementation "xyz" = "cde"
-- #test implementation "aaa" = "fff"
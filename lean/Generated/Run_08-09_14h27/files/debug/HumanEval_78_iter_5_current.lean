/- 
function_signature: "def hex_key(num: string) -> int"
docstring: |
    You have been tasked to write a function that receives
    a hexadecimal number as a string and counts the number of hexadecimal
    digits that are primes (prime number, or a prime, is a natural number
    greater than 1 that is not a product of two smaller natural numbers).
    Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
    Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
    So you have to determine a number of the following digits: 2, 3, 5, 7,
    B (=decimal 11), D (=decimal 13).
    Note: you may assume the input is always correct or empty string,
    and symbols A,B,C,D,E,F are always uppercase.
test_cases:
  - input: "AB"
    expected_output: 1
  - input: "1077E"
    expected_output: 2
  - input: "ABED1A33"
    expected_output: 4
  - input: "123456789ABCDEF0"
    expected_output: 6
  - input: "2020"
    expected_output: 2
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def hex_to_nat (ch : Char) : Nat :=
  if ch.isDigit then
    (ch.toNat - '0'.toNat)
  else if ch.isUpper then
    ((ch.toNat - 'A'.toNat) + 10)
  else 0

-- LLM HELPER
def is_prime_hex_digit (ch : Char) : Bool :=
  let val := hex_to_nat ch
  val = 2 || val = 3 || val = 5 || val = 7 || val = 11 || val = 13

def implementation (num: String) : Int :=
  (num.toList.filter is_prime_hex_digit).length

-- LLM HELPER
lemma hex_to_nat_digit (ch : Char) (h : ch.isDigit) : 
  hex_to_nat ch = ch.toNat - '0'.toNat := by
  unfold hex_to_nat
  simp [h]

-- LLM HELPER
lemma hex_to_nat_upper (ch : Char) (h : ch.isUpper) (h2 : ¬ch.isDigit) : 
  hex_to_nat ch = (ch.toNat - 'A'.toNat) + 10 := by
  unfold hex_to_nat
  simp [h2, h]

-- LLM HELPER
lemma num_val_eq_hex_to_nat (ch : Char) :
  (if ch.isDigit then
      (ch.toNat - '0'.toNat)
    else if ch.isUpper then
      ((ch.toNat - 'A'.toNat) + 10)
    else 0) = hex_to_nat ch := by
  unfold hex_to_nat
  rfl

-- LLM HELPER
lemma not_prime_small_values (n : Nat) (h : n < 2) : ¬Nat.Prime n := by
  cases n with
  | zero => norm_num
  | succ n => 
    cases n with
    | zero => norm_num
    | succ n => omega

-- LLM HELPER
lemma not_prime_composite_values (n : Nat) (h : n ∈ [4, 6, 8, 9, 10, 12, 14, 15]) : ¬Nat.Prime n := by
  simp at h
  cases h with
  | inl h => rw [h]; norm_num
  | inr h => cases h with
    | inl h => rw [h]; norm_num
    | inr h => cases h with
      | inl h => rw [h]; norm_num
      | inr h => cases h with
        | inl h => rw [h]; norm_num
        | inr h => cases h with
          | inl h => rw [h]; norm_num
          | inr h => cases h with
            | inl h => rw [h]; norm_num
            | inr h => cases h with
              | inl h => rw [h]; norm_num
              | inr h => rw [h]; norm_num

-- LLM HELPER
lemma hex_digit_bound_digit (ch : Char) (h : ch.isDigit = true) : hex_to_nat ch ≤ 9 := by
  unfold hex_to_nat
  simp [h]
  have char_bound : ch.toNat - '0'.toNat ≤ 9 := by
    have : '0'.toNat ≤ ch.toNat ∧ ch.toNat ≤ '9'.toNat := by
      simp [Char.isDigit] at h
      exact h
    omega
  exact char_bound

-- LLM HELPER
lemma hex_digit_bound_upper (ch : Char) (h : ch.isUpper = true) (h2 : ch.isDigit = false) : 10 ≤ hex_to_nat ch ∧ hex_to_nat ch ≤ 15 := by
  unfold hex_to_nat
  simp [h2, h]
  have : 'A'.toNat ≤ ch.toNat ∧ ch.toNat ≤ 'F'.toNat := by
    simp [Char.isUpper] at h
    exact h
  omega

-- LLM HELPER  
lemma bool_not_true_eq_false (b : Bool) : ¬(b = true) ↔ (b = false) := by
  cases b <;> simp

-- LLM HELPER
lemma prime_iff_is_prime_hex_digit (ch : Char) :
  Nat.Prime (hex_to_nat ch) ↔ is_prime_hex_digit ch = true := by
  unfold is_prime_hex_digit
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases h1 : hex_to_nat ch = 2
    · simp [h1]
    · by_cases h2 : hex_to_nat ch = 3  
      · simp [h2]
      · by_cases h3 : hex_to_nat ch = 5
        · simp [h3]
        · by_cases h4 : hex_to_nat ch = 7
          · simp [h4]
          · by_cases h5 : hex_to_nat ch = 11
            · simp [h5]
            · by_cases h6 : hex_to_nat ch = 13
              · simp [h6]
              · exfalso
                have bound : hex_to_nat ch ≤ 15 := by
                  by_cases hd : ch.isDigit = true
                  · have : hex_to_nat ch ≤ 9 := hex_digit_bound_digit ch hd
                    omega
                  · by_cases hu : ch.isUpper = true
                    · have : 10 ≤ hex_to_nat ch ∧ hex_to_nat ch ≤ 15 := hex_digit_bound_upper ch hu hd
                      omega
                    · unfold hex_to_nat
                      simp [hd, hu]
                      omega
                interval_cases (hex_to_nat ch)
                · exact not_prime_small_values 0 (by norm_num) h
                · exact not_prime_small_values 1 (by norm_num) h
                · exact h1 rfl
                · exact h2 rfl
                · exact not_prime_composite_values 4 (by simp) h
                · exact h3 rfl
                · exact not_prime_composite_values 6 (by simp) h
                · exact h4 rfl
                · exact not_prime_composite_values 8 (by simp) h
                · exact not_prime_composite_values 9 (by simp) h
                · exact not_prime_composite_values 10 (by simp) h
                · exact h5 rfl
                · exact not_prime_composite_values 12 (by simp) h
                · exact h6 rfl
                · exact not_prime_composite_values 14 (by simp) h
                · exact not_prime_composite_values 15 (by simp) h
  · intro h
    simp at h
    cases h with
    | inl h => rw [h]; norm_num
    | inr h => cases h with
      | inl h => rw [h]; norm_num
      | inr h => cases h with
        | inl h => rw [h]; norm_num
        | inr h => cases h with
          | inl h => rw [h]; norm_num
          | inr h => cases h with
            | inl h => rw [h]; norm_num
            | inr h => rw [h]; norm_num

def problem_spec
-- function signature
(implementation: String → Int)
-- inputs
(num: String) :=
-- spec
let spec (result: Int) :=
  let num_val (ch : Char) :=
    if ch.isDigit then
      (ch.toNat - '0'.toNat)
    else if ch.isUpper then
      ((ch.toNat - 'A'.toNat) + 10)
    else 0;
  0 < num.length →
  (
    let char_val := num_val num.toList[0]!;
    (Nat.Prime char_val →
      (1 < num.length → result = char_val + implementation (num.drop 1)) ∧
      (1 = num.length → result = char_val)) ∧
    (¬Nat.Prime char_val →
      (1 < num.length → result = implementation (num.drop 1)) ∧
      (1 = num.length → result = 0))
  )
-- program termination
∃ result, implementation num = result ∧
spec result

theorem correctness
(num: String)
: problem_spec implementation num := by
  unfold problem_spec
  use implementation num
  constructor
  · rfl
  · intro h_pos
    have count_eq : implementation num = ↑(List.filter is_prime_hex_digit num.data).length := by
      unfold implementation
      simp [String.toList]
    simp only [num_val_eq_hex_to_nat]
    by_cases h_prime : Nat.Prime (hex_to_nat (num.data[0]?.getD 'A'))
    · simp [h_prime]
      have prime_char : is_prime_hex_digit (num.data[0]?.getD 'A') = true := by
        rw [← prime_iff_is_prime_hex_digit]
        exact h_prime
      constructor
      · intro h_multi
        have : hex_to_nat (num.data[0]?.getD 'A') = ↑(List.filter is_prime_hex_digit num.data).length := by
          simp [count_eq.symm, implementation]
        rw [this]
        simp
      · intro h_single
        simp [h_single, count_eq]
        have : num.data.length = 1 := by simp [String.length] at h_single; exact h_single
        simp [this]
        simp [prime_char]
    · simp [h_prime]
      have not_prime_char : is_prime_hex_digit (num.data[0]?.getD 'A') = false := by
        rw [prime_iff_is_prime_hex_digit] at h_prime
        rw [Bool.not_eq_true] at h_prime
        exact h_prime
      constructor
      · intro h_multi
        simp [count_eq]
      · intro h_single
        simp [count_eq, h_single]
        have : num.data.length = 1 := by simp [String.length] at h_single; exact h_single
        simp [this, not_prime_char]
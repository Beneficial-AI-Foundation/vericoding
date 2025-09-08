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
lemma prime_iff_is_prime_hex_digit (ch : Char) :
  Nat.Prime (hex_to_nat ch) ↔ is_prime_hex_digit ch = true := by
  unfold is_prime_hex_digit
  constructor
  · intro h
    have h_val := h
    unfold hex_to_nat at h_val
    split_ifs at h_val with h1 h2
    · -- digit case
      have : hex_to_nat ch ≤ 9 := by
        unfold hex_to_nat
        simp [h1]
        sorry -- bound on digit values
      interval_cases (hex_to_nat ch) <;> simp at h_val
    · -- upper case  
      have : 10 ≤ hex_to_nat ch ∧ hex_to_nat ch ≤ 15 := by
        unfold hex_to_nat
        simp [h1, h2]
        sorry -- bound on hex values
      interval_cases (hex_to_nat ch) <;> simp at h_val ⊢
    · -- else case
      have : hex_to_nat ch = 0 := by unfold hex_to_nat; simp [h1, h2]
      rw [this] at h_val
      norm_num at h_val
  · intro h
    unfold is_prime_hex_digit at h
    simp only [Bool.or_eq_true] at h
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
    have h_first : num.toList[0]! = num.toList.head (by simp [List.length_pos_iff_exists_mem.mp (by simpa using h_pos)]) := by
      simp [List.get_zero]
    rw [num_val_eq_hex_to_nat]
    rw [h_first]
    have h_eq : (num.toList.filter is_prime_hex_digit).length = 
      (if is_prime_hex_digit num.toList.head then 1 else 0) + 
      (num.toList.tail.filter is_prime_hex_digit).length := by
      cases num.toList with
      | nil => simp at h_pos
      | cons hd tl => 
        simp [List.filter_cons]
        split_ifs with h
        · simp
        · simp
    cases h_prime : Nat.Prime (hex_to_nat num.toList.head) with
    | false =>
      constructor
      · intro h_contra
        contradiction
      · constructor
        · intro h_len
          unfold implementation
          rw [h_eq]
          have : ¬is_prime_hex_digit num.toList.head := by
            rw [← prime_iff_is_prime_hex_digit]
            exact h_prime
          simp [this]
          sorry -- relate tail to drop 1
        · intro h_len
          unfold implementation  
          rw [h_eq]
          have : ¬is_prime_hex_digit num.toList.head := by
            rw [← prime_iff_is_prime_hex_digit]
            exact h_prime
          simp [this]
          have : num.toList.tail = [] := by
            have : num.toList.length = 1 := by
              simp [String.length] at h_len
              exact h_len
            cases num.toList with
            | nil => simp at h_pos
            | cons hd tl => 
              simp at this
              simp [this]
          simp [this]
    | true =>
      constructor
      · constructor
        · intro h_len
          unfold implementation
          rw [h_eq] 
          have : is_prime_hex_digit num.toList.head := by
            rw [prime_iff_is_prime_hex_digit]
            exact h_prime
          simp [this]
          sorry -- relate tail to drop 1 and show char_val = 1
        · intro h_len
          unfold implementation
          rw [h_eq]
          have : is_prime_hex_digit num.toList.head := by
            rw [prime_iff_is_prime_hex_digit] 
            exact h_prime
          simp [this]
          have : num.toList.tail = [] := by
            have : num.toList.length = 1 := by
              simp [String.length] at h_len
              exact h_len  
            cases num.toList with
            | nil => simp at h_pos
            | cons hd tl =>
              simp at this
              simp [this]
          simp [this]
          sorry -- show char_val = hex_to_nat head
      · intro h_not_prime
        contradiction

-- #test implementation "AB" = 1
-- #test implementation "1077E" = 2
-- #test implementation "ABED1A33" = 4
-- #test implementation "2020" = 2
-- #test implementation "123456789ABCDEF0" = 6
-- #test implementation "112233445566778899AABBCCDDEEFF00" = 12
-- #test implementation "" = 0
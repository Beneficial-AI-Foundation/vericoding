/-
We have two special characters. The first character can be represented by one bit 0. The second character can be represented by two bits (10 or 11).  

Now given a string represented by several bits. Return whether the last character must be a one-bit character or not. The given string will always end with a zero.

Example 1:

Input: 
bits = [1, 0, 0]
Output: True
Explanation: 
The only way to decode it is two-bit character and one-bit character. So the last character is one-bit character.

Example 2:

Input: 
bits = [1, 1, 1, 0]
Output: False
Explanation: 
The only way to decode it is two-bit character and two-bit character. So the last character is NOT one-bit character.

Note:
1 .
bits[i] is always 0 or 1.
-/

def countTrailingOnes : List Nat → Nat
  | [] => 0
  | xs => sorry

-- <vc-helpers>
-- </vc-helpers>

def is_one_bit_character (bits : List Nat) : Bool :=
  sorry

theorem ends_with_zero {bits : List Nat} (h : bits ≠ []) : 
  bits.getLast (by exact h) = 0 → 
  is_one_bit_character bits = true ∨ is_one_bit_character bits = false :=
sorry

theorem all_zeros_is_true {bits : List Nat} (h : bits ≠ []) :
  (bits.all (fun x => x = 0)) →
  is_one_bit_character bits = true :=
sorry

theorem trailing_ones_parity {bits : List Nat} (h : bits.length ≥ 2) :
  is_one_bit_character bits = (countTrailingOnes (bits.dropLast) % 2 = 0) :=
sorry

theorem edge_cases_hold :
  (is_one_bit_character [0] = true) ∧ 
  (is_one_bit_character [0, 0] = true) :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_one_bit_character [1, 0, 0]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_one_bit_character [1, 1, 1, 0]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_one_bit_character [0, 0]

-- Apps difficulty: introductory
-- Assurance level: unguarded
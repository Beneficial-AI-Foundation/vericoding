-- <vc-preamble>
def strong_num (n : Nat) : String := sorry

def factorial (n : Nat) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumDigitFactorials (n : Nat) : Nat := sorry

def digitsOfNat (n : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem strong_num_outputs_valid_string (n : Nat) :
  (strong_num n = "STRONG!!!!" ∨ strong_num n = "Not Strong !!") := sorry

theorem strong_num_correctness (n : Nat) :
  (strong_num n = "STRONG!!!!" ↔ sumDigitFactorials n = n) := sorry

theorem single_digit_strong_nums (n : Nat) :
  n ≤ 9 →
  (strong_num n = "STRONG!!!!" ↔ (n = 1 ∨ n = 2)) := sorry

theorem digit_composition_property (digits : List Nat) :
  (∀ d ∈ digits, d ≤ 9) →
  let n := sorry -- conversion of digits to number
  (strong_num n = "STRONG!!!!" ↔ (sumDigitFactorials n = n)) := sorry

/-
info: 'STRONG!!!!'
-/
-- #guard_msgs in
-- #eval strong_num 145

/-
info: 'Not Strong !!'
-/
-- #guard_msgs in
-- #eval strong_num 123

/-
info: 'STRONG!!!!'
-/
-- #guard_msgs in
-- #eval strong_num 40585
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
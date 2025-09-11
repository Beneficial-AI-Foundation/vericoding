-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largestMultipleOfThree (digits : List Nat) : Option String := sorry

def stringToNat (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_multiple_of_three (digits : List Nat) :
  ∀ result : String,
  largestMultipleOfThree digits = some result →
  (stringToNat result % 3 = 0) := sorry

theorem result_uses_valid_digits (digits : List Nat) :
  ∀ result : String,
  largestMultipleOfThree digits = some result →
  ∀ d : Nat,
  (result.data.count (Char.ofNat d)) ≤ (digits.count d) := sorry

theorem handles_leading_zeros (digits : List Nat) :
  ∀ result : String,
  largestMultipleOfThree digits = some result →
  (result = "0" ∨ result.data.get! 0 ≠ '0') := sorry

/-
info: '981'
-/
-- #guard_msgs in
-- #eval largest_multiple_of_three [9, 8, 1]

/-
info: '8760'
-/
-- #guard_msgs in
-- #eval largest_multiple_of_three [8, 6, 7, 1, 0]

/-
info: ''
-/
-- #guard_msgs in
-- #eval largest_multiple_of_three [1]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
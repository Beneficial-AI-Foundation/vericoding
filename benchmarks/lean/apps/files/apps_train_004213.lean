-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abundant_number (n : Nat) : Bool := sorry

def divisors_sum (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem abundant_number_is_bool (n : Nat) : 
  abundant_number n = true ∨ abundant_number n = false := sorry

theorem abundant_number_matches_definition (n : Nat) :
  abundant_number n = (divisors_sum n > n) := sorry 

theorem abundant_number_true_implies_sum_greater (n : Nat) :
  abundant_number n = true → divisors_sum n > n := sorry

theorem abundant_number_false_implies_sum_leq (n : Nat) :
  abundant_number n = false → divisors_sum n ≤ n := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval abundant_number 12

/-
info: False
-/
-- #guard_msgs in
-- #eval abundant_number 37

/-
info: True
-/
-- #guard_msgs in
-- #eval abundant_number 120
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
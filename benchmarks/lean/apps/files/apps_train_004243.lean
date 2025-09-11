-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_number (n : Int) : Int := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sign_preserved (x : Int) : 
  x ≥ 0 → reverse_number x ≥ 0 ∧ 
  x < 0 → reverse_number x < 0 := 
  sorry

theorem trailing_zeros_removed (x n : Nat) :
  x > 0 → 
  n ≥ 0 →
  n ≤ 5 →
  reverse_number (x * 10^n) = 
    reverse_number x :=
  sorry

/-
info: 321
-/
-- #guard_msgs in
-- #eval reverse_number 123

/-
info: -654
-/
-- #guard_msgs in
-- #eval reverse_number -456

/-
info: 1
-/
-- #guard_msgs in
-- #eval reverse_number 1000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
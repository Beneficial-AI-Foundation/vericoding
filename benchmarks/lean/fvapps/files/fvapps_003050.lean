-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_unknown_number (x y z : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_unknown_number_range (x y z : Nat) (h1 : x ≤ 1000) (h2 : y ≤ 1000) (h3 : z ≤ 1000) :
  1 ≤ find_unknown_number x y z ∧ find_unknown_number x y z ≤ 105 := by
  sorry

theorem find_unknown_number_modulo (x y z : Nat) (h1 : x ≤ 1000) (h2 : y ≤ 1000) (h3 : z ≤ 1000) :
  (find_unknown_number x y z) % 3 = (70*x + 21*y + 15*z) % 3 ∧
  (find_unknown_number x y z) % 5 = (70*x + 21*y + 15*z) % 5 ∧
  (find_unknown_number x y z) % 7 = (70*x + 21*y + 15*z) % 7 := by
  sorry

theorem find_unknown_number_zeros :
  find_unknown_number 0 0 0 = 105 := by
  sorry
-- </vc-theorems>
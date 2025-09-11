-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_minimum_sum_pair (n: Nat) : Nat := sorry

def isPrime (n: Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_is_positive (n: Nat) (h: n ≥ 1) :
  find_minimum_sum_pair n > 0 := sorry

theorem prime_input_returns_plus_one (n: Nat) (h: n ≥ 1) :
  isPrime n = true → find_minimum_sum_pair n = n + 1 := sorry

theorem even_number_property (n: Nat) (h: n ≥ 2) :
  n % 2 = 0 → find_minimum_sum_pair n ≤ 2 + n/2 := sorry

theorem one_returns_two :
  find_minimum_sum_pair 1 = 2 := sorry

/-
info: 1929
-/
-- #guard_msgs in
-- #eval find_minimum_sum_pair 852140

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_minimum_sum_pair 12

/-
info: 18
-/
-- #guard_msgs in
-- #eval find_minimum_sum_pair 17
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
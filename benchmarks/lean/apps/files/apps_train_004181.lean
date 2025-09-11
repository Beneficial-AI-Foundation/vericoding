-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find (n : Nat) (z : Nat) : Nat := sorry

def bucket_digit_distributions_total_sum (n : Nat) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_result_larger_than_input (n : Nat) (z : Nat) (h1 : n > 0) (h2 : n ≤ 10000) (h3 : z ≤ 1000) :
  find n z > n := sorry

theorem find_is_minimal_solution (n : Nat) (z : Nat) (h1 : n > 0) (h2 : n ≤ 10000) (h3 : z ≤ 1000) :
  let result := find n z
  bucket_digit_distributions_total_sum (result - 1) ≤ bucket_digit_distributions_total_sum n + z ∧
  bucket_digit_distributions_total_sum result > bucket_digit_distributions_total_sum n + z := sorry

theorem bucket_digit_distributions_properties (n : Nat) (h1 : n > 0) (h2 : n ≤ 10000) :
  bucket_digit_distributions_total_sum n ≥ -n := sorry

/-
info: 888
-/
-- #guard_msgs in
-- #eval find 500 200

/-
info: 10003
-/
-- #guard_msgs in
-- #eval find 10001 100

/-
info: 30046
-/
-- #guard_msgs in
-- #eval find 30000 1000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
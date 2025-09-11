-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def somethingAcci (num_digits: Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_length_at_least_six (n: Nat) : (somethingAcci n).1 ≥ 6 :=
  sorry

theorem final_digit_length_meets_request (n: Nat) : (somethingAcci n).2 ≥ n :=
  sorry

theorem sequence_grows_monotonically {n: Nat} (h: n > 1) : 
  (somethingAcci n).1 ≥ (somethingAcci (n-1)).1 ∧ 
  (somethingAcci n).2 ≥ (somethingAcci (n-1)).2 :=
  sorry

/-
info: (10, 8)
-/
-- #guard_msgs in
-- #eval something_acci 5

/-
info: (11, 14)
-/
-- #guard_msgs in
-- #eval something_acci 10

/-
info: (12, 25)
-/
-- #guard_msgs in
-- #eval something_acci 20
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
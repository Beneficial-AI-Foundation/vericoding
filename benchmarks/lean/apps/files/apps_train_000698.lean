-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_roses (boys girls : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem roses_is_even (boys girls : Nat) (h1 : boys > 0) (h2 : girls > 0) :
  2 ∣ calculate_roses boys girls :=
  sorry

theorem roses_is_nonnegative (boys girls : Nat) (h1 : boys > 0) (h2 : girls > 0) :
  calculate_roses boys girls ≥ 0 :=
  sorry

theorem roses_formula (boys girls : Nat) (h1 : boys > 0) (h2 : girls > 0) :
  calculate_roses boys girls = 2 * ((boys + girls) - 1) :=
  sorry

theorem equal_boys_girls (n : Nat) (h : n > 0) :
  calculate_roses n n = 2 * (2 * n - 1) :=
  sorry

theorem minimum_case :
  calculate_roses 1 1 = 2 :=
  sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval calculate_roses 2 3

/-
info: 10
-/
-- #guard_msgs in
-- #eval calculate_roses 3 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_roses 1 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
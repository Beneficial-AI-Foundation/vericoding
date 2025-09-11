-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def productsum (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem productsum_basic_cases :
  productsum 2 = 4 ∧ productsum 3 = 10 ∧ productsum 4 = 18 :=
  sorry

theorem productsum_positive (n: Nat) (h: n ≥ 2) :
  productsum n > 0 :=
  sorry

theorem productsum_increases (n: Nat) (h: n ≥ 2) :
  productsum (n + 1) > productsum n :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval productsum 3

/-
info: 30
-/
-- #guard_msgs in
-- #eval productsum 6

/-
info: 4
-/
-- #guard_msgs in
-- #eval productsum 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
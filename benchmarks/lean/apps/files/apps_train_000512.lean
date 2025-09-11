-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_remainder (a b c : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_remainder_bounded
  (a b c : Nat)
  (h1 : a > 0)
  (h2 : b < a)
  (h3 : c > 0) :
  solve_remainder a b c ≤ c :=
sorry

theorem solve_remainder_mod
  (a b c : Nat)
  (h1 : a > 0)
  (h2 : b < a)
  (h3 : c > 0) :
  solve_remainder a b c % a = b :=
sorry

theorem solve_remainder_largest
  (a b c : Nat)
  (h1 : a > 0)
  (h2 : b < a)
  (h3 : c > 0) :
  let next := solve_remainder a b c + a
  next > c ∨ next % a ≠ b :=
sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_remainder 7 2 10

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_remainder 5 3 12

/-
info: 95
-/
-- #guard_msgs in
-- #eval solve_remainder 10 5 100
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
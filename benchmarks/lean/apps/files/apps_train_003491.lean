-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def code (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem code_non_negative (a b : Nat) :
  0 ≤ code a b := by
  sorry

theorem code_commutative (a b : Nat) :
  code a b = code b a := by
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval code 9 8

/-
info: 1419
-/
-- #guard_msgs in
-- #eval code 123 456

/-
info: 1698
-/
-- #guard_msgs in
-- #eval code 200 100
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
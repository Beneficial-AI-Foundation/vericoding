-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rectangle_rotation (a b : Nat) : Nat := sorry

theorem always_positive
  (a b : Nat)
  (h1 : a > 0)
  (h2 : b > 0)
  (h3 : a ≤ 1000)
  (h4 : b ≤ 1000) :
  rectangle_rotation a b > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetry
  (a b : Nat)
  (h1 : a > 0)
  (h2 : b > 0)
  (h3 : a ≤ 1000)
  (h4 : b ≤ 1000) :
  rectangle_rotation a b = rectangle_rotation b a := sorry

/-
info: 23
-/
-- #guard_msgs in
-- #eval rectangle_rotation 6 4

/-
info: 65
-/
-- #guard_msgs in
-- #eval rectangle_rotation 30 2

/-
info: 49
-/
-- #guard_msgs in
-- #eval rectangle_rotation 8 6
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
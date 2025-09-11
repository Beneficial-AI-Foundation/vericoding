-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transform_triple (p q r a b c : Int) : Int := sorry

theorem identity_transform_is_zero (x y z : Int) : 
  transform_triple x y z x y z = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positive_differences_sum 
  (p q r a b c : Nat) :
  let result := transform_triple p q r a b c
  (result ≠ -1) →
  result = (max 0 (a - p) + max 0 (b - q) + max 0 (c - r)) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval transform_triple 2 2 1 3 3 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval transform_triple 2 2 2 2 2 2

/-
info: -1
-/
-- #guard_msgs in
-- #eval transform_triple 5 5 5 4 4 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
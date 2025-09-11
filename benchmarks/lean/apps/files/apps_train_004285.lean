-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_product (l: List Int) : Option Int := sorry

theorem max_product_symmetric (nums: List Int) :
  max_product nums = max_product nums.reverse := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 20
-/
-- #guard_msgs in
-- #eval max_product [2, 1, 5, 0, 4, 3]

/-
info: 72
-/
-- #guard_msgs in
-- #eval max_product [7, 8, 9]

/-
info: 104874
-/
-- #guard_msgs in
-- #eval max_product [33, 231, 454, 11, 9, 99, 57]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
-- <vc-helpers>
-- </vc-helpers>

def maximum_product (nums : List Int) : Int := sorry

theorem maximum_product_scales {nums : List Int} (h : nums.length ≥ 3) (scale : Int) (h2 : scale > 0) :
  maximum_product (nums.map (· * scale)) = maximum_product nums * (scale * scale * scale) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval maximum_product [1, 2, 3]

/-
info: 24
-/
-- #guard_msgs in
-- #eval maximum_product [1, 2, 3, 4]

/-
info: 720
-/
-- #guard_msgs in
-- #eval maximum_product [-4, -3, -2, -1, 60]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
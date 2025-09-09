def List.product (l : List Int) : Int := sorry 

def product_sans_n (nums : List Int) : List Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def count_zeros (l : List Int) : Nat :=
  l.filter (· = 0) |>.length

theorem product_sans_n_length {nums : List Int} (h : nums ≠ []) : 
  (product_sans_n nums).length = nums.length := sorry

/-
info: [24, 12, 8, 6]
-/
-- #guard_msgs in
-- #eval product_sans_n [1, 2, 3, 4]

/-
info: [0, -18, 0]
-/
-- #guard_msgs in
-- #eval product_sans_n [9, 0, -2]

/-
info: [0, 0, 0]
-/
-- #guard_msgs in
-- #eval product_sans_n [0, -99, 0]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
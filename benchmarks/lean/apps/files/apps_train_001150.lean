-- <vc-helpers>
-- </vc-helpers>

def min_menus_for_price (price : Nat) : Nat := sorry

def bin_ones (n : Nat) : Nat := sorry

-- The result is always positive

theorem min_menus_positive (price : Nat) 
  (h : price > 0) (h₂ : price ≤ 1000000) : 
  min_menus_for_price price > 0 := sorry

-- The result is never more than binary ones plus 2048s

theorem min_menus_binary_bound (price : Nat) 
  (h : price > 0) (h₂ : price ≤ 1000000) :
  min_menus_for_price price ≤ bin_ones (price % 2048) + (price / 2048) := sorry

-- Powers of 2 up to 2048 require exactly 1 menu

theorem power_two_property (price : Nat) 
  (h : price > 0) (h₂ : price ≤ 2048)
  (h₃ : ∃ k, price = 2^k) :
  min_menus_for_price price = 1 := sorry

-- Edge cases

theorem edge_case_2048 : min_menus_for_price 2048 = 1 := sorry

theorem edge_case_4096 : min_menus_for_price 4096 = 2 := sorry

theorem edge_case_2047 : min_menus_for_price 2047 = 11 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_menus_for_price 10

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_menus_for_price 256

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_menus_for_price 4096

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
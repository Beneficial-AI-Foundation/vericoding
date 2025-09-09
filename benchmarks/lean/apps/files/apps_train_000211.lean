def isGoodArray (nums : List Nat) : Bool := sorry

def gcd (a b : Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def listGcd (nums : List Nat) : Nat := sorry

theorem good_array_gcd {nums : List Nat} (h : nums ≠ []) :
  isGoodArray nums = true ↔ listGcd nums = 1
  := sorry

theorem multiples_not_good {n : Nat} (h : n ≥ 2) : 
  isGoodArray [n, 2*n, 3*n, 4*n] = false 
  := sorry

theorem scale_makes_not_good {nums : List Nat} (h : nums ≠ []) :
  isGoodArray (nums.map (· * 2)) = false
  := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval isGoodArray #[12, 5, 7, 23]

/-
info: True
-/
-- #guard_msgs in
-- #eval isGoodArray #[29, 6, 10]

/-
info: False
-/
-- #guard_msgs in
-- #eval isGoodArray #[3, 6]

-- Apps difficulty: interview
-- Assurance level: unguarded
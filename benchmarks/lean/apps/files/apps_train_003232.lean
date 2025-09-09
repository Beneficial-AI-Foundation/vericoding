def products (n : Nat) (k m : Nat) : List (List Nat) := sorry

def eq_dice (dice : List Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def List.prod (l : List Nat) : Nat := sorry

theorem eq_dice_single_die (n : Nat) 
  (h : 3 ≤ n ∧ n ≤ 20) :
  eq_dice [n] = (products n 3 (min (n-1) 20)).length := sorry

theorem eq_dice_small_pairs (d1 d2 : Nat)
  (h1 : 3 ≤ d1 ∧ d1 ≤ 6)
  (h2 : 3 ≤ d2 ∧ d2 ≤ 6) :
  eq_dice [d1, d2] ≤ 5 := sorry

theorem eq_dice_threes :
  eq_dice [3, 3] = 0 := sorry

theorem eq_dice_four :
  eq_dice [4] = (products 4 3 3).length := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval eq_dice [6, 6]

/-
info: 5
-/
-- #guard_msgs in
-- #eval eq_dice [5, 6, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval eq_dice [3, 3]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
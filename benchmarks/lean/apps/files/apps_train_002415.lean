-- <vc-helpers>
-- </vc-helpers>

def arrangeCoins (n: Nat) : Nat := sorry

theorem arrange_coins_valid_input (n: Nat) (h: n ≥ 1) :
  let result := arrangeCoins n
  result ≥ 1 ∧ 
  result * (result + 1) / 2 ≤ n ∧
  (result + 1) * (result + 2) / 2 > n := sorry

theorem arrange_coins_monotonic (n: Nat) (h: n ≥ 1) :
  arrangeCoins (n + 1) ≥ arrangeCoins n := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval arrange_coins 5

/-
info: 3
-/
-- #guard_msgs in
-- #eval arrange_coins 8

/-
info: 1
-/
-- #guard_msgs in
-- #eval arrange_coins 1

-- Apps difficulty: introductory
-- Assurance level: guarded
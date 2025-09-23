-- <vc-preamble>
def List.sum : List Nat → Nat 
| [] => 0
| (x::xs) => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_conquest (n m : Nat) (armies : List Nat) : BattleResult := sorry

theorem check_conquest_valid_result (n m : Nat) (armies : List Nat) :
  check_conquest n m armies = BattleResult.VICTORY ∨ 
  check_conquest n m armies = BattleResult.DEFEAT := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_conquest_enough_armies (n m : Nat) (armies : List Nat) :
  n ≤ m → check_conquest n m armies = BattleResult.VICTORY := sorry

theorem check_conquest_insufficient_armies (n m : Nat) (armies : List Nat) :
  n > m → (List.take m armies).sum ≤ 0 → 
  check_conquest n m armies = BattleResult.DEFEAT := sorry

theorem check_conquest_monotone (n m : Nat) (armies : List Nat) :
  n > m →
  check_conquest n m armies = BattleResult.VICTORY →
  check_conquest n m (armies.map (· + 1)) = BattleResult.VICTORY := sorry

/-
info: 'VICTORY'
-/
-- #guard_msgs in
-- #eval check_conquest 5 3 [1, 2, 3, 4, 5]

/-
info: 'VICTORY'
-/
-- #guard_msgs in
-- #eval check_conquest 6 2 [4, 4, 4, 4, 4, 4]

/-
info: 'DEFEAT'
-/
-- #guard_msgs in
-- #eval check_conquest 7 4 [10, 10, 10, 10, 50, 60, 70]
-- </vc-theorems>
-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def stone_game_ii (piles : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stone_game_ii_positive (piles : List Nat) 
  (h : piles.all (λ x => x > 0)) :
  stone_game_ii piles > 0 :=
sorry

theorem stone_game_ii_bounded (piles : List Nat) :
  stone_game_ii piles ≤ List.sum piles :=
sorry  

theorem stone_game_ii_singleton (pile : Nat) 
  (h : pile > 0) : 
  stone_game_ii [pile] = pile :=
sorry

theorem stone_game_ii_same_values (x : Nat)
  (h : x > 0) :
  stone_game_ii [x, x, x] ≤ 3 * x :=
sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval stone_game_ii [2, 7, 9, 4, 4]

/-
info: 1
-/
-- #guard_msgs in
-- #eval stone_game_ii [1]

/-
info: 15
-/
-- #guard_msgs in
-- #eval stone_game_ii [8, 7, 1, 2]
-- </vc-theorems>
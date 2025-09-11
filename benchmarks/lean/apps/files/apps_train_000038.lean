-- <vc-preamble>
def maximum (l : List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_card_game (n k1 k2 : Nat) (arr1 arr2 : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem card_game_returns_bool (n k1 k2 : Nat) (arr1 arr2 : List Int) 
  (h1 : k1 > 0) (h2 : k2 > 0) (h3 : arr1.length > 0) (h4 : arr2.length > 0) :
  solve_card_game n k1 k2 arr1 arr2 = true ∨ 
  solve_card_game n k1 k2 arr1 arr2 = false :=
sorry

theorem card_game_compares_maxes (n k1 k2 : Nat) (arr1 arr2 : List Int)
  (h1 : k1 > 0) (h2 : k2 > 0) (h3 : arr1.length > 0) (h4 : arr2.length > 0) :
  solve_card_game n k1 k2 arr1 arr2 = (maximum arr1 > maximum arr2) :=
sorry

theorem empty_lists_error (n : Nat) :
  ∀ (arr1 arr2 : List Int), 
  arr1.length = 0 → arr2.length = 0 → 
  solve_card_game n 0 0 arr1 arr2 = default :=
sorry

theorem equal_maxes_false (n k1 k2 : Nat) (arr1 arr2 : List Int)
  (h1 : arr1.length > 0) (h2 : arr2.length > 0)
  (h3 : maximum arr2 = maximum arr1) :
  solve_card_game n arr1.length arr2.length arr1 arr2 = false :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval solve_card_game 2 1 1 [2] [1]

/-
info: False
-/
-- #guard_msgs in
-- #eval solve_card_game 5 2 3 [2, 3] [1, 4, 5]

/-
info: True
-/
-- #guard_msgs in
-- #eval solve_card_game 3 1 2 [3] [1, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
-- <vc-preamble>
def List.sum (l : List Nat) : Nat :=
  match l with 
  | [] => 0
  | h :: t => h + sum t

def List.sort (l : List Nat) : List Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_card_game (input : String) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_card_game_upper_bound {n k : Nat} {cards : List Nat} 
  (h1 : k ≤ n) (h2 : cards.length = n) :
  solve_card_game s!"${n} ${k} ${cards}" ≤ cards.sum :=
  sorry

theorem solve_card_game_lower_bound {n k : Nat} {cards : List Nat}
  (h1 : k ≤ n) (h2 : cards.length = n) :
  solve_card_game s!"${n} ${k} ${cards}" ≥ (cards.sort.reverse.take k).sum :=
  sorry

theorem solve_card_game_nonneg {n k : Nat} {cards : List Nat}
  (h1 : k ≤ n) (h2 : cards.length = n) :
  solve_card_game s!"${n} ${k} ${cards}" ≥ 0 :=
  sorry

theorem solve_card_game_single_card {n : Nat} :
  solve_card_game s!"1 1 ${n}" = n :=
  sorry

theorem solve_card_game_invalid_empty :
  solve_card_game "" = 0 :=
  sorry

theorem solve_card_game_invalid_format :
  solve_card_game "a b c" = 0 :=
  sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve_card_game "4 2 1 2 3 4"

/-
info: 12
-/
-- #guard_msgs in
-- #eval solve_card_game test2

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_card_game test3
-- </vc-theorems>
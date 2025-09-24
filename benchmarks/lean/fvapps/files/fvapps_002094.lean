-- <vc-preamble>
def sum (l: List Nat) : Nat := 
  match l with
  | [] => 0
  | h::t => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_stone_game (n : Nat) (stones : List Nat) : String := sorry

-- Properties for solve_stone_game
-- </vc-definitions>

-- <vc-theorems>
theorem solve_stone_game_valid_output (n : Nat) (stones : List Nat) :
  let result := solve_stone_game n stones
  result = "T" ∨ result = "HL" := sorry

theorem solve_stone_game_majority_stone (n : Nat) (stones : List Nat) :
  let total := sum stones
  (∃ x ∈ stones, x * 2 > total) →
  solve_stone_game n stones = "T" := sorry

theorem solve_stone_game_odd_sum (n : Nat) (stones : List Nat) :
  sum stones % 2 ≠ 0 →
  solve_stone_game n stones = "T" := sorry

theorem solve_stone_game_even_sum_no_majority (n : Nat) (stones : List Nat) :
  sum stones % 2 = 0 →
  (∀ x ∈ stones, x * 2 ≤ sum stones) →
  solve_stone_game n stones = "HL" := sorry

theorem solve_stone_game_single (stone : Nat) :
  stone > 0 →
  solve_stone_game 1 [stone] = "T" := sorry

theorem solve_stone_game_equal_stones_even (n : Nat) :
  n % 2 = 0 →
  solve_stone_game n (List.replicate n 1) = "HL" := sorry

theorem solve_stone_game_equal_stones_odd (n : Nat) :
  n % 2 ≠ 0 →
  solve_stone_game n (List.replicate n 1) = "T" := sorry
-- </vc-theorems>
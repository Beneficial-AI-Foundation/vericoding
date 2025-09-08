/-
# Task
 You have some people who are betting money, and they all start with the same amount of money (this number>0). 

 Find out if the given end-state of amounts is possible after the betting is over and money is redistributed.

# Input/Output

 - `[input]` integer array arr

  the proposed end-state showing final amounts for each player

 - `[output]` a boolean value

  `true` if this is a possible end-state and `false` otherwise

# Examples

- For `arr = [0, 56, 100]`, the output should be `true`.

Three players start with the same amount of money 52.

At the end of game, player 1 lose `52`, player2 win `4`, and  player3 win `48`.

- For `arr = [0, 0, 0]`, the output should be `false`.

Players should start with a positive number of of money.

- For `arr = [11]`, the output should be `true`.

One player always keep his money at the end of game.

- For `arr = [100, 100, 100, 90, 1, 0, 0]`, the output should be `false`.

These players can not start with the same amount of money.
-/

def List.sum (xs : List Int) : Int := 
  xs.foldl (· + ·) 0

-- <vc-helpers>
-- </vc-helpers>

def learn_charitable_game (arr : List Int) : Bool := sorry

theorem single_element_validity {n : Int} :
  learn_charitable_game [n] = (n > 0) := sorry

theorem non_positive_sum_invalid {arr : List Int} (h : arr.sum ≤ 0) :
  learn_charitable_game arr = false := sorry

theorem divisible_sum_valid {arr : List Int} (h₁ : arr.sum > 0) :
  learn_charitable_game arr = (arr.sum % arr.length == 0) := sorry

theorem all_zeros_invalid {arr : List Int} 
  (h₁ : arr.length ≥ 2)
  (h₂ : ∀ x ∈ arr, x = 0) :
  learn_charitable_game arr = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval learn_charitable_game [0, 56, 100]

/-
info: False
-/
-- #guard_msgs in
-- #eval learn_charitable_game [0, 0, 0]

/-
info: True
-/
-- #guard_msgs in
-- #eval learn_charitable_game [11]

-- Apps difficulty: introductory
-- Assurance level: unguarded
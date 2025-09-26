-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_dice_tower (nums : List Nat) : List String := sorry

theorem solve_dice_tower_returns_yes_no_list {nums : List Nat} :
  let result := solve_dice_tower nums 
  result.length = nums.length ∧ 
  ∀ x ∈ result, x = "YES" ∨ x = "NO" :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiples_of_seven_return_no {n : Nat} (h : n % 7 = 0) :
  solve_dice_tower [n] = ["NO"] := 
sorry

theorem numbers_less_than_fifteen_return_no {n : Nat} (h : n < 15) :
  solve_dice_tower [n] = ["NO"] :=
sorry

theorem odd_quotient_returns_no {n : Nat} (h1 : n ≥ 15) (h2 : (n / 7) % 2 = 1) :
  solve_dice_tower [n] = ["NO"] :=
sorry

theorem valid_numbers_return_yes {n : Nat} 
  (h1 : n ≥ 15) 
  (h2 : n % 7 ≠ 0) 
  (h3 : (n / 7) % 2 ≠ 1) :
  solve_dice_tower [n] = ["YES"] :=
sorry
-- </vc-theorems>
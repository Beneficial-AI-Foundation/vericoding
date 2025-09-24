-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def how_many_pizzas (n: Nat) : String := sorry

theorem how_many_pizzas_format (n: Nat) (h: n ≤ 1000) :
  let result := how_many_pizzas n
  result.startsWith "pizzas: " ∧ 
  result.length > 8 ∧
  (result.drop 8 |>.startsWith ", slices: ") = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem how_many_pizzas_values_nonnegative (n: Nat) (h: n ≤ 1000) :
  let result := how_many_pizzas n
  let pizzas := (result.splitOn ", ").get! 0 |>.splitOn ": " |>.get! 1 |>.toNat!
  let slices := (result.splitOn ": ").get! 2 |>.toNat!
  pizzas ≥ 0 ∧ 0 ≤ slices ∧ slices < 8 := sorry

theorem how_many_pizzas_math (n: Nat) (h: n ≤ 1000) :
  let total_area := n * n
  let expected_pizzas := total_area / 64
  let expected_slices := (total_area / 8) % 8
  let result := how_many_pizzas n
  let actual_pizzas := (result.splitOn ", ").get! 0 |>.splitOn ": " |>.get! 1 |>.toNat!
  let actual_slices := (result.splitOn ": ").get! 2 |>.toNat!
  actual_pizzas = expected_pizzas ∧ actual_slices = expected_slices := sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Island := List Nat

def solve_recipes (islands: List Island) (num_ingredients: Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_recipes_minimal_result_type (islands: List Island) (num_ingredients: Nat):
  num_ingredients = 2 →
  (∀ i ∈ islands, ∀ x ∈ i.tail, x ≤ 2) →
  let result := solve_recipes islands num_ingredients
  result = "sad" ∨ result = "some" ∨ result = "all" := sorry

theorem solve_recipes_minimal_insufficient_ingredients (islands: List Island) (num_ingredients: Nat):
  num_ingredients = 2 →
  (∀ i ∈ islands, ∀ x ∈ i.tail, x ≤ 2) →
  (let ingredients := List.foldl (fun acc i => List.foldl (fun s x => x :: s) acc i.tail) [] islands;
   ingredients.length < num_ingredients) →
  solve_recipes islands num_ingredients = "sad" := sorry
-- </vc-theorems>
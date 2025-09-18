-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_highest_priority_recipe (recipes: List String) (priorities: List Int) (queries: List String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem recipe_result_length (recipes: List String) (priorities: List Int) (queries: List String) :
  recipes.length = priorities.length →
  (find_highest_priority_recipe recipes priorities queries).length = queries.length :=
  sorry

theorem result_contents (recipes: List String) (priorities: List Int) (queries: List String) : 
  recipes.length = priorities.length →
  ∀ r ∈ find_highest_priority_recipe recipes priorities queries, 
    r = "NO" ∨ r ∈ recipes :=
  sorry

theorem empty_inputs :
  find_highest_priority_recipe [] [] [] = [] ∧
  find_highest_priority_recipe ["recipe"] [1] [] = [] :=
  sorry
-- </vc-theorems>
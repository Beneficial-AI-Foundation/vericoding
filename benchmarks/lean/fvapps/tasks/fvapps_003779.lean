-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def tacofy (word : String) : List String := sorry

def VALID_INGREDIENTS : List String := ["tomato", "lettuce", "cheese", "guacamole", "salsa", "beef"]
-- </vc-definitions>

-- <vc-theorems>
theorem tacofy_always_has_shells (word : String) :
  let result := tacofy word
  result.head? = some "shell" ∧ 
  result.getLast? = some "shell" ∧
  result.length ≥ 2 := sorry 

theorem tacofy_valid_ingredients (word : String) :
  let result := tacofy word
  let middle := result.drop 1 |>.dropLast
  ∀ ing ∈ middle, ing ∈ VALID_INGREDIENTS := sorry
-- </vc-theorems>
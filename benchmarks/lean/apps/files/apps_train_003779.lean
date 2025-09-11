-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: ['shell', 'shell']
-/
-- #guard_msgs in
-- #eval tacofy ""

/-
info: ['shell', 'beef', 'guacamole', 'lettuce', 'shell']
-/
-- #guard_msgs in
-- #eval tacofy "ogl"

/-
info: ['shell', 'beef', 'tomato', 'lettuce', 'cheese', 'guacamole', 'salsa', 'shell']
-/
-- #guard_msgs in
-- #eval tacofy "abtlcgs"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
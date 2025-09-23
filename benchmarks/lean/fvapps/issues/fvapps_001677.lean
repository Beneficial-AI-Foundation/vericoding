-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rpg : List (List Char) → List Action → Option GameState := sorry

theorem valid_field_movements {field : List (List Char)} {actions : List Action} 
    (h : rpg field actions ≠ none) :
  let result := (rpg field actions).get!
  ∃ dir, dir ∈ ['<', '>', '^', 'v'] ∧ 
  dir ∈ result.field.join := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem item_collection {field : List (List Char)} {actions : List Action}
    (h : rpg field actions ≠ none) :
  let result := (rpg field actions).get!
  result.attack ≥ 1 ∧ result.defense ≥ 1 := sorry

theorem health_bounds {field : List (List Char)} {actions : List Action}
    (h : rpg field actions ≠ none) :
  let result := (rpg field actions).get!
  1 ≤ result.health ∧ result.health ≤ 3 := sorry

theorem merchant_interaction {field : List (List Char)} {actions : List Action}
    (h : rpg field actions ≠ none) :
  let result := (rpg field actions).get!
  'C' ∉ result.bag := sorry

theorem combat_outcome {field : List (List Char)} {actions : List Action}
    (h : rpg field actions ≠ none)
    (h2 : field.length > 0)
    (h3 : field[0]!.length > 0) :
  let result := (rpg field actions).get!
  result.field[0]![0]! = ' ' ∨ field[0]![0]! = 'E' := sorry
-- </vc-theorems>
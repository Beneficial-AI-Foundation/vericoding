-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def colourAssociation {α β : Type} (pairs : List (α × β)) : List (Dict α β) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem colourAssociation_length_eq
  {α β : Type} [Inhabited α] [Inhabited β]
  (pairs : List (α × β))
  (h : pairs.length > 0) :
  (colourAssociation pairs).length = pairs.length :=
sorry

theorem colourAssociation_valid_structure
  {α β : Type} [Inhabited α] [Inhabited β]
  (pairs : List (α × β))
  (h : pairs.length > 0)
  (i : Nat)
  (hi : i < pairs.length) :
  let result := colourAssociation pairs
  have hi' : i < result.length := by
    rw [colourAssociation_length_eq pairs h]
    exact hi
  (result[i]'hi').keys.length = 1 ∧ 
  (result[i]'hi').values.length = 1 ∧
  (result[i]'hi').keys[0]! = (pairs[i]'hi).1 ∧
  (result[i]'hi').values[0]! = (pairs[i]'hi).2 :=
sorry

theorem colourAssociation_maintains_order
  {α β : Type} [Inhabited α] [Inhabited β]
  (pairs : List (α × β))
  (h : pairs.length > 0)
  (i : Nat)
  (hi : i < pairs.length) :
  let result := colourAssociation pairs
  have hi' : i < result.length := by
    rw [colourAssociation_length_eq pairs h]
    exact hi
  (result[i]'hi').keys[0]! = (pairs[i]'hi).1 :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval colour_association [["white", "goodness"], ["blue", "tranquility"]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval colour_association [["red", "energy"], ["yellow", "creativity"]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval colour_association [["gray", "intelligence"], ["black", "classy"]]
-- </vc-theorems>
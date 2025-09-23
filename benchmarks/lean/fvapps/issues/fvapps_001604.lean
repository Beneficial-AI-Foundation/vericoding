-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def same_structure_as {α β : Type} (x : NestedList α) (y : NestedList β) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_structure_reflexive {α : Type} (x : NestedList α) :
  same_structure_as x x = true :=
  sorry

theorem same_structure_value_independent {α β : Type} (x : NestedList α) (y : NestedList β) :
  same_structure_as x y = true ∨ same_structure_as x y = false :=
  sorry

theorem same_structure_symmetric {α β : Type} (x : NestedList α) (y : NestedList β) :
  same_structure_as x y = same_structure_as y x :=
  sorry

theorem flat_vs_nested_mismatch {α β : Type} (l : List (NestedList α)) (b : β) :
  l ≠ [] →
  same_structure_as (NestedList.node l) (NestedList.leaf b) = false :=
  sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval same_structure_as [1, [1, 1]] [[2, 2], 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval same_structure_as [1, [1, 1]] [2, [2, 2]]

/-
info: True
-/
-- #guard_msgs in
-- #eval same_structure_as [[[], []]] [[[], []]]
-- </vc-theorems>
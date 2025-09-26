-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def NestedList.depth {α : Type} : NestedList α → Nat
  | elem _ => sorry
  | list _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flat_list_depth {α : Type} (l : List α) : 
  NestedList.depth (NestedList.list (l.map NestedList.elem)) = 1 := sorry

theorem list_depth_lower_bound {α : Type} (nl : NestedList α) :
  NestedList.depth nl ≥ 1 := sorry

theorem nested_list_depth_greater {α : Type} (outer : NestedList α) (inner : NestedList α)
  (h : inner ≠ outer) : 
  NestedList.depth outer > NestedList.depth inner := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval list_depth [1, [2, [3, [4, [5, [6], 5], 4], 3], 2], 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval list_depth [2, "yes", [True, False]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval list_depth [2.0, [2, 0], 3.7, [3, 7], 6.7, [6, 7]]
-- </vc-theorems>
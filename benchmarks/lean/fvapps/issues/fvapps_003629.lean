-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def deep_count {α : Type} (l : NestedList α) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem deep_count_nonnegative {α : Type} (l : NestedList α) :
  deep_count l ≥ 0 :=
sorry

theorem deep_count_geq_outer_length {α : Type} (l : List (NestedList α)) :
  deep_count (NestedList.list l) ≥ l.length :=
sorry

theorem deep_count_flat_list {α : Type} (l : List α) :
  deep_count (NestedList.list (l.map NestedList.elem)) = l.length :=
sorry

theorem deep_count_nested_list {α : Type} (outer : List (List α)) :
  deep_count (NestedList.list (outer.map (fun inner => NestedList.list (inner.map NestedList.elem)))) =
  outer.length + (outer.foldl (fun acc l => acc + l.length) 0) :=
sorry

theorem deep_count_empty {α : Type} :
  deep_count (NestedList.list ([] : List (NestedList α))) = 0 :=
sorry

theorem deep_count_empty_nested {α : Type} :
  deep_count (NestedList.list [NestedList.list ([] : List (NestedList α))]) = 1 :=
sorry

theorem deep_count_two_empty {α : Type} :
  deep_count (NestedList.list [NestedList.list ([] : List (NestedList α)), NestedList.list ([] : List (NestedList α))]) = 2 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval deep_count [1, 2, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval deep_count ["x", "y", ["z"]]

/-
info: 7
-/
-- #guard_msgs in
-- #eval deep_count [1, 2, [3, 4, [5]]]
-- </vc-theorems>
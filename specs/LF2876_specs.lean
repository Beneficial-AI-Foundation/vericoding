-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def locate {α : Type u} [BEq α] : NestedList α → α → Bool := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem locate_returns_bool {α : Type u} [BEq α] (seq : NestedList α) (value : α) :
  locate seq value = true ∨ locate seq value = false :=
sorry

theorem locate_finds_root_value {α : Type u} [BEq α] (seq : List (NestedList α)) (value : α) :
  locate (NestedList.list (seq ++ [NestedList.elem value])) value = true :=
sorry

theorem locate_handles_missing_value {α : Type u} [BEq α] (seq : List (NestedList α)) (value : α)
  (h : ∀ x ∈ seq, ¬∃ inner, x = NestedList.list inner) : 
  (∀ x ∈ seq, x ≠ NestedList.elem value) → locate (NestedList.list seq) value = false :=
sorry

theorem locate_finds_nested_value {α : Type u} [BEq α] (seq : NestedList α) (value : α) :
  locate (NestedList.list [seq, NestedList.list [NestedList.elem value]]) value = true := 
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval locate ["a", "b", ["c", "d", ["e"]]] "a"

/-
info: True
-/
-- #guard_msgs in
-- #eval locate ["a", "b", ["c", "d", ["e"]]] "e"

/-
info: False
-/
-- #guard_msgs in
-- #eval locate ["a", "b", ["c", "d", ["e"]]] "f"
-- </vc-theorems>
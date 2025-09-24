-- <vc-preamble>
def stringify {α : Type} [ToString α] : Node α → String :=
  sorry

def make_linked_list {α : Type} : List α → Node α :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitOnStr (s : String) (sep : String) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem stringify_matches_list_structure {α : Type} [ToString α] (items : List α) :
  let ll := make_linked_list items
  let result := stringify ll
  let parts := splitOnStr result " -> "
  if items.isEmpty then
    result = "None"
  else
    parts.getLast! = "None" ∧
    parts.length - 1 = items.length ∧
    parts.take items.length = items.map ToString.toString :=
  sorry

theorem stringify_outputs_well_formed {α : Type} [ToString α] (items : List α) :
  let ll := make_linked_list items
  let result := stringify ll
  let parts := splitOnStr result " -> "
  result.endsWith "None" ∧
  parts.all (·.trim ≠ "") ∧
  (if items.isEmpty then
    parts.length = 1
  else
    parts.length = items.length + 1) :=
  sorry

/-
info: 'None'
-/
-- #guard_msgs in
-- #eval stringify None

/-
info: '1 -> None'
-/
-- #guard_msgs in
-- #eval stringify Node(1)

/-
info: '1 -> 2 -> 3 -> None'
-/
-- #guard_msgs in
-- #eval stringify Node(1, Node(2, Node(3)))
-- </vc-theorems>
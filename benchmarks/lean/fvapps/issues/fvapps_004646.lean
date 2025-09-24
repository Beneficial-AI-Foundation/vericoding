-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_to_array {α : Type} : LinkedList α → List α
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem list_to_array_preserves_values {α : Type} (l : LinkedList α) :
  list_to_array l = LinkedList.rec [] (fun head tail arr => head :: arr) l :=
sorry

theorem list_to_array_maintains_order {α : Type} [Inhabited α] (l : LinkedList α) :
  ∀ i < (list_to_array l).length,
    (list_to_array l).get ⟨i, by sorry⟩ = LinkedList.rec default (fun head tail res => head) l :=
sorry

theorem list_to_array_empty {α : Type} :
  list_to_array (@LinkedList.nil α) = @List.nil α :=
sorry

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval list_to_array LinkedList(1, LinkedList(2, LinkedList(3)))

/-
info: ['hello', True, 42]
-/
-- #guard_msgs in
-- #eval list_to_array LinkedList("hello", LinkedList(True, LinkedList(42)))

/-
info: ['solo']
-/
-- #guard_msgs in
-- #eval list_to_array LinkedList("solo")
-- </vc-theorems>
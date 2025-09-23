-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unique (α : Type) [BEq α] : List α → List α := sorry

theorem unique_order (α : Type) [BEq α] (l : List α) :
  let r := unique α l
  (∀ x ∈ r, x ∈ l) ∧ 
  (List.Nodup r) ∧
  (∀ x y, List.indexOf r x < List.indexOf r y → List.indexOf l x < List.indexOf l y) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unique_properties (α : Type) [BEq α] (l : List α) :
  let r := unique α l
  (∀ x ∈ r, x ∈ l) ∧ 
  (∀ x ∈ l, (x ∈ r)) ∧ 
  (r.length ≤ l.length) :=
sorry 

theorem unique_empty (α : Type) [BEq α] : unique α [] = [] := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval unique []

/-
info: [5, 2, 1, 3]
-/
-- #guard_msgs in
-- #eval unique [5, 2, 1, 3]

/-
info: [1, 5, 2, 0, -3, 10]
-/
-- #guard_msgs in
-- #eval unique [1, 5, 2, 0, 2, -3, 1, 10]
-- </vc-theorems>
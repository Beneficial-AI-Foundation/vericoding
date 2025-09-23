-- <vc-preamble>
def List.toBag {α : Type u} [BEq α] (l : List α) : Bag α where
  count a := List.length (List.filter (fun x => x == a) l)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_by_perfsq (arr : List Nat) : List Nat := sorry

theorem sort_by_perfsq_maintains_length {arr : List Nat} :
  List.length (sort_by_perfsq arr) = List.length arr := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_by_perfsq_maintains_elements {arr : List Nat} :
  (sort_by_perfsq arr).toBag = arr.toBag := sorry

theorem sort_by_perfsq_idempotent {arr : List Nat} :
  sort_by_perfsq (sort_by_perfsq arr) = sort_by_perfsq arr := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval sort_by_perfsq [715, 112, 136, 169, 144]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval sort_by_perfsq [234, 61, 16, 441, 144, 728]
-- </vc-theorems>
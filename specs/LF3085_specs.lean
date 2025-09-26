-- <vc-preamble>
def count (xs : List α) (a : α) : Nat :=
  xs.foldl (fun acc x => if x = a then acc + 1 else acc) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def majority : List α → Option α := sorry

theorem majority_exists {arr : List α} {x : α}
  (h : count arr x > arr.length / 2) :
  majority arr = some x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem majority_empty :
  majority ([] : List α) = none := sorry

theorem majority_single_element {arr : List α} {x : α}
  (h_nonempty : arr ≠ [])
  (h_all_same : ∀ i, arr.get ⟨i, sorry⟩ = x) :
  majority arr = some x := sorry

/-
info: 'A'
-/
-- #guard_msgs in
-- #eval majority ["A", "B", "A"]

/-
info: None
-/
-- #guard_msgs in
-- #eval majority ["A", "B", "C"]

/-
info: None
-/
-- #guard_msgs in
-- #eval majority []
-- </vc-theorems>
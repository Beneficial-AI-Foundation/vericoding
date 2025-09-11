-- <vc-preamble>
def min_ops_to_sort {α : Type u} [Ord α] (arr : List α) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSorted {α : Type u} [Ord α] [LE α] (xs : List α) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: rest => x ≤ y ∧ isSorted (y :: rest)
-- </vc-definitions>

-- <vc-theorems>
theorem translation_invariant (arr : List Int) (k : Int) :
  min_ops_to_sort arr = min_ops_to_sort (arr.map (fun x => x + k)) :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_ops_to_sort [4, 7, 2, 2, 9]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_ops_to_sort [3, 5, 8, 1, 7]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_ops_to_sort [1, 2, 2, 4, 5]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
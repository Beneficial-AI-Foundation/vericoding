-- <vc-helpers>
-- </vc-helpers>

def solution {α : Type} [BEq α] : List α → Bool
  | xs => sorry

theorem solution_matches_manual {α : Type} [BEq α] (xs : List α) :
  solution xs = ∃ i j : Nat, i < j ∧ j < xs.length ∧ xs[i]? = xs[j]? := by sorry

theorem empty_and_single_no_duplicates {α : Type} [BEq α] (xs : List α) :
  xs.length ≤ 1 → solution xs = false := by sorry

theorem all_same_has_duplicates {α : Type} [BEq α] (x : α) (n : Nat) :
  n ≥ 2 → solution (List.replicate n x) = true := by sorry

theorem order_independent {α : Type} [BEq α] (xs : List α) :
  solution xs = solution xs.reverse := by sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval solution 1 2 3

/-
info: True
-/
-- #guard_msgs in
-- #eval solution 1 2 3 2

/-
info: True
-/
-- #guard_msgs in
-- #eval solution "a" "b" "c" "c"

-- Apps difficulty: introductory
-- Assurance level: unguarded
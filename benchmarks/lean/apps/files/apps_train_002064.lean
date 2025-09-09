def List.maximum (l: List Nat) : Nat :=
match l with
| [] => 0
| (x::xs) => List.foldl Nat.max x xs

-- <vc-helpers>
-- </vc-helpers>

def min_max_generating_set (numbers: List Nat) : List Nat :=
sorry

theorem one_in_gen_set (numbers: List Nat) (h: numbers ≠ []) : 
  1 ∈ min_max_generating_set numbers :=
sorry

theorem max_output_bounded (numbers: List Nat) (h: numbers ≠ []) :
  ∀ x ∈ min_max_generating_set numbers, x ≤ List.maximum numbers :=
sorry

theorem output_size_bounded (numbers: List Nat) :
  List.length (min_max_generating_set numbers) ≤ List.length numbers :=
sorry

/-
info: {1, 2, 3, 4, 5}
-/
-- #guard_msgs in
-- #eval set min_max_generating_set(input1)

/-
info: {1, 3, 7, 12, 13, 14}
-/
-- #guard_msgs in
-- #eval set min_max_generating_set(input2)

/-
info: {1, 2, 3, 4, 5, 6}
-/
-- #guard_msgs in
-- #eval set min_max_generating_set(input3)

-- Apps difficulty: competition
-- Assurance level: unguarded
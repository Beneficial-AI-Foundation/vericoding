-- <vc-preamble>
def List.sum (xs : List Nat) : Nat :=
match xs with
| [] => 0
| x::xs => x + xs.sum
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_eligible_students (N M K : Nat) (student_data : List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_eligible_students_empty_data
  {N M K : Nat} (h1 : N ≥ 1) (h2 : M ≥ 1) (h3 : K ≥ 1) :
  count_eligible_students N M K [] = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_eligible_students 4 8 4 [[1, 2, 1, 2, 5], [3, 5, 1, 3, 4], [1, 2, 4, 5, 11], [1, 1, 1, 3, 12]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_eligible_students 2 10 2 [[1, 2, 11], [2, 3, 12]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_eligible_students 2 5 2 [[2, 4, 5], [3, 3, 2]]
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_ops_to_sort (arr : List Nat) : Nat := sorry

theorem min_ops_non_negative (arr : List Nat) :
  min_ops_to_sort arr ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_ops_upper_bound {arr : List Nat} :
  min_ops_to_sort arr ≤ List.length (List.eraseDups arr) := sorry 

theorem min_ops_all_same {arr : List Nat} :
  List.length (List.eraseDups arr) = 1 → min_ops_to_sort arr = 0 := sorry

theorem min_ops_single_elem {arr : List Nat} :
  List.length arr = 1 → min_ops_to_sort arr = 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_ops_to_sort [3, 1, 6, 6, 3, 1, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_ops_to_sort [1, 1, 4, 4, 4, 7, 8, 8]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_ops_to_sort [4, 2, 5, 2, 6, 2, 7]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
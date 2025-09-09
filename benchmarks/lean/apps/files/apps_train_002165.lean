-- <vc-helpers>
-- </vc-helpers>

def solve_perm_sort (perm : List Nat) : Bool := sorry

theorem identity_permutation_valid {n : Nat} (perm : List Nat)
  (h : perm = List.range n) : 
  solve_perm_sort perm = true := sorry

theorem result_is_boolean (perm : List Nat) :
  solve_perm_sort perm = true ∨ solve_perm_sort perm = false := sorry 

theorem reversed_sequence_property {n : Nat} (perm : List Nat) 
  (h : perm = (List.range n).reverse) :
  solve_perm_sort perm = (n ≤ 3) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval solve_perm_sort [5, 2, 1, 4, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval solve_perm_sort [3, 2, 4, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval solve_perm_sort [3, 2, 1, 6, 5, 4, 7]

-- Apps difficulty: competition
-- Assurance level: unguarded
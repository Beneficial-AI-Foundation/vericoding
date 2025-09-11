-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_xor (n : Nat) (arr : List Nat) : Nat := sorry

theorem xor_self_cancel (x : Nat) : 
  solve_array_xor 2 [x, x] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem xor_commutative (n : Nat) (arr : List Nat) : 
  solve_array_xor n arr = solve_array_xor n arr.reverse := sorry

theorem xor_zero_identity (x : Nat) : 
  solve_array_xor 2 [x, 0] = x := sorry

theorem single_element (x : Nat) :
  solve_array_xor 1 [x] = x := sorry

theorem even_duplicates_zero (x : Nat) :
  solve_array_xor 4 [x, x, x, x] = 0 := sorry

theorem odd_duplicates_self (x : Nat) :
  solve_array_xor 3 [x, x, x] = x := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_array_xor 5 [8, 4, 1, 5, 0]

/-
info: 15
-/
-- #guard_msgs in
-- #eval solve_array_xor 5 [1, 2, 4, 0, 8]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_array_xor 2 [10, 10]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
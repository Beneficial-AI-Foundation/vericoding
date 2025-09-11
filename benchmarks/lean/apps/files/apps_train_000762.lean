-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_xorgon (n k : Nat) (arr : List Nat) : Nat := sorry

theorem solve_xorgon_properties (n k : Nat) (arr : List Nat)
  (h1 : arr.length > 0) (h2 : k > 0) :
  let result := solve_xorgon n k arr
  (result ≥ 0 ∧ result ≤ arr.length) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_xorgon_empty_array (n k : Nat) (arr : List Nat) 
  (h : arr.length = 0) :
  solve_xorgon 0 k arr = 0 := sorry

theorem solve_xorgon_result_bounded (n k : Nat) (arr : List Nat)
  (h : arr.length > 0) :
  solve_xorgon n k arr ≤ arr.length := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_xorgon 7 5 [1, 0, 0, 1, 1, 1, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_xorgon 4 3 [1, 1, 0, 0]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_xorgon 3 3 [0, 0, 0]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_pattern (k : Nat) : List String := sorry

theorem test_base_case :
  solve_pattern 1 = ["1"] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem test_pattern_props {k : Nat} (h : k > 0) (h2 : k ≤ 10) :
  let result := solve_pattern k
  -- Number of rows equals k
  List.length result = k ∧  
  -- First row is 1..k concatenated
  List.head! result = toString k ∧ 
  -- Each element is a string containing only digits
  ∀ x ∈ result, ∃ n : Nat, toString n = x
  := sorry

/-
info: ['1']
-/
-- #guard_msgs in
-- #eval solve_pattern 1

/-
info: ['12', '34']
-/
-- #guard_msgs in
-- #eval solve_pattern 2

/-
info: ['123', '456', '789']
-/
-- #guard_msgs in
-- #eval solve_pattern 3

/-
info: ['1234', '5678', '9101112', '13141516']
-/
-- #guard_msgs in
-- #eval solve_pattern 4
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
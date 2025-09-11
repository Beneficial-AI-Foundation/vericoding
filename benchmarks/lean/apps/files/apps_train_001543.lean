-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveMaxScore (n: Nat) (p: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solveMaxScore_nonnegative (n p : Nat) :
  n > 0 → p > 0 → solveMaxScore n p ≥ 0 := by
  sorry

theorem solveMaxScore_equal_inputs (n : Nat) :
  n > 0 → 
  let d := n % (n/2 + 1)
  if d = 0 then
    solveMaxScore n n = n * n * n 
  else 
    solveMaxScore n n = (n-d)*(n-d) + (n-d)*(n-n) + (n-n)*(n-n) := by
  sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval solve_max_score 4 4

/-
info: 13
-/
-- #guard_msgs in
-- #eval solve_max_score 3 4

/-
info: 27
-/
-- #guard_msgs in
-- #eval solve_max_score 2 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded
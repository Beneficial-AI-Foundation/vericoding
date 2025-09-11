-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Nat) (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_bounded (x : Nat) (s : String) :
  0 ≤ solve x s ∧ solve x s < 10^9 + 7
  := sorry

theorem solve_deterministic (x : Nat) (s : String) :
  solve x s = solve x s
  := sorry

theorem solve_examples_correct :
  solve 5 "231" = 25 ∧ 
  solve 7 "2323" = 1438 ∧
  solve 6 "333" = 1101
  := sorry

/-
info: 25
-/
-- #guard_msgs in
-- #eval solve 5 "231"

/-
info: 1438
-/
-- #guard_msgs in
-- #eval solve 7 "2323"

/-
info: 1101
-/
-- #guard_msgs in
-- #eval solve 6 "333"
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded
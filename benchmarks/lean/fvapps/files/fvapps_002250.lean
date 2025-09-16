-- <vc-preamble>
def solve_sequence_sum (n m : Nat) (sequence : List Nat) : Nat :=
  sorry

abbrev M : Nat := 1000000007
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + list_sum xs
-- </vc-definitions>

-- <vc-theorems>
theorem solve_sequence_sum_nonneg (n m : Nat) (sequence : List Nat) :
  solve_sequence_sum n m sequence ≥ 0 :=
  sorry

theorem solve_sequence_sum_special_case :
  solve_sequence_sum 1 1 [0] = 2 :=
  sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_sequence_sum 3 5 [1, 2, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_sequence_sum 1 1 [0]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
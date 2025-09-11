-- <vc-preamble>
def solve_psychos (n : Nat) (arr : List Nat) : Nat :=
  sorry

def is_sorted_desc (arr : List Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_strictly_sorted_asc (arr : List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_single_array :
  solve_psychos 0 [] = 0 ∧ 
  ∀ x : Nat, solve_psychos 1 [x] = 0 :=
sorry

theorem solve_psychos_bounds :
  ∀ (n : Nat) (arr : List Nat),
  arr.length = n →
  0 ≤ solve_psychos n arr ∧ 
  solve_psychos n arr ≤ n - 1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_psychos 10 [10, 9, 7, 8, 6, 5, 3, 4, 2, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_psychos 6 [1, 2, 3, 4, 5, 6]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_psychos 6 [6, 5, 4, 3, 2, 1]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
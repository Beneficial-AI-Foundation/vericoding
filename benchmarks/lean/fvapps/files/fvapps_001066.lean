-- <vc-preamble>
def nc3 (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (c : Nat) (k : Nat) (lines : List (List Nat)) (v : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nc3_nonnegative (n : Nat) :
  nc3 n ≥ 0 :=
  sorry

theorem nc3_zero_for_small_n (n : Nat) : 
  n < 3 → nc3 n = 0 :=
  sorry

theorem nc3_formula (n : Nat) :
  nc3 n = n * (n-1) * (n-2) / 6 :=
  sorry

theorem solve_nonnegative (n c k : Nat) (lines : List (List Nat)) (v : List Nat) :
  solve n c k lines v ≥ 0 :=
  sorry

theorem solve_bounded_by_combinations 
  (n c k : Nat) (lines : List (List Nat)) (v : List Nat)
  (validLines := List.filter (fun line => line.get! 2 ≤ c) lines) :
  solve n c k lines v ≤ nc3 validLines.length :=
  sorry

theorem solve_empty :
  solve 0 1 1 [] [1] = 0 :=
  sorry

theorem solve_minimal :
  solve 1 1 1 [[0,0,1]] [1] = 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 7 2 13 [[1, 10, 1], [1, 14, 2], [6, 4, 1], [2, 2, 1], [0, 12, 2], [2, 11, 2], [0, 6, 1]] [8, 10]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve 6 1 20 [[1, 5, 1], [2, 11, 1], [4, 0, 1], [6, 8, 1], [0, 11, 1], [3, 3, 1]] [9]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
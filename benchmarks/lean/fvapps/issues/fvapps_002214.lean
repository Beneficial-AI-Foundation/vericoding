-- <vc-preamble>
def solve (n : Nat) (a : List Nat) : GameResult :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidResult (result : GameResult) : Bool :=
  match result with
  | GameResult.WIN => true
  | GameResult.LOSE => true
  | GameResult.DRAW => true
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_is_valid {n : Nat} {a : List Nat} (h: n > 0) (h2: a.length = n):
  isValidResult (solve n a) = true := by
  sorry

theorem solve_consistent_result {n : Nat} {a : List Nat} (h: n > 0) (h2: a.length = n):
  solve n a = solve n a := by
  sorry

theorem solve_invariant_under_reordering {n : Nat} {a b : List Nat} 
  (h: n > 0) (h2: a.length = n) (h3: b.length = n)
  (h4: ∃ p : List Nat, b = p ++ a):
  solve n a = solve n b := by
  sorry

theorem solve_all_same_numbers {n : Nat} {val : Nat} (h: n > 0):
  isValidResult (solve n (List.replicate n val)) = true := by
  sorry

/-
info: 'WIN'
-/
-- #guard_msgs in
-- #eval solve 3 [1, 2, 2]

/-
info: 'LOSE'
-/
-- #guard_msgs in
-- #eval solve 3 [2, 2, 3]

/-
info: 'DRAW'
-/
-- #guard_msgs in
-- #eval solve 5 [0, 0, 0, 2, 2]
-- </vc-theorems>
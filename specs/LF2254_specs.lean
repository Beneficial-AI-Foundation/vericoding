-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_min_team_diff (n : Nat) (strengths : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_team_diff_non_negative (n : Nat) (strengths : List Int)
  (h1 : n ≥ 2)
  (h2 : strengths.length ≥ n) :
  solve_min_team_diff n strengths ≥ 0 :=
sorry

theorem min_team_diff_upper_bound (n : Nat) (strengths : List Int)
  (h1 : n ≥ 2)
  (h2 : strengths.length ≥ n) :
  solve_min_team_diff n strengths ≤ (List.maximum? strengths).getD 0 - (List.minimum? strengths).getD 0 :=
sorry

theorem min_team_diff_is_minimum (n : Nat) (strengths : List Int)
  (h1 : n ≥ 2)  
  (h2 : strengths.length ≥ n) :
  ∃ min_diff : Int,
    solve_min_team_diff n strengths = min_diff ∧
    ∀ (x y : Int), x ∈ strengths → y ∈ strengths → x ≤ y → min_diff ≤ y - x :=
sorry

theorem min_team_diff_two_elements (a b : Int) :
  solve_min_team_diff 2 [a, b] = Int.natAbs (b - a) :=
sorry

theorem min_team_diff_identical {x : Int} {n : Nat} (lst : List Int)
  (h1 : n ≥ 2)
  (h2 : lst.length = n)
  (h3 : ∀ (i : Fin lst.length), lst.get i = x) :
  solve_min_team_diff n lst = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_min_team_diff 5 [3, 1, 2, 6, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_min_team_diff 6 [2, 1, 3, 2, 4, 3]

/-
info: 999
-/
-- #guard_msgs in
-- #eval solve_min_team_diff 2 [1, 1000]
-- </vc-theorems>
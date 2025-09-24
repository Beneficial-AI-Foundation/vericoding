-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_race (x1 x2 x3 v1 v2 : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_race_returns_valid_result (x1 x2 x3 : Int) (v1 v2 : Int) 
  (h1 : 1 ≤ v1 ∧ v1 ≤ 100) (h2 : 1 ≤ v2 ∧ v2 ≤ 100)
  (h3 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (h4 : -1000 ≤ x2 ∧ x2 ≤ 1000)
  (h5 : -1000 ≤ x3 ∧ x3 ≤ 1000) :
  solve_race x1 x2 x3 v1 v2 = "Chef" ∨ 
  solve_race x1 x2 x3 v1 v2 = "Kefa" ∨
  solve_race x1 x2 x3 v1 v2 = "Draw" :=
  sorry

theorem solve_race_symmetric (x1 x2 x3 : Int) (v1 v2 : Int)
  (h1 : 1 ≤ v1 ∧ v1 ≤ 100) (h2 : 1 ≤ v2 ∧ v2 ≤ 100)
  (h3 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (h4 : -1000 ≤ x2 ∧ x2 ≤ 1000)
  (h5 : -1000 ≤ x3 ∧ x3 ≤ 1000) :
  (solve_race x1 x2 x3 v1 v2 = "Chef" → solve_race x2 x1 x3 v2 v1 = "Kefa") ∧
  (solve_race x1 x2 x3 v1 v2 = "Kefa" → solve_race x2 x1 x3 v2 v1 = "Chef") ∧
  (solve_race x1 x2 x3 v1 v2 = "Draw" → solve_race x2 x1 x3 v2 v1 = "Draw") :=
  sorry

theorem solve_race_same_position_same_speed (x1 x3 : Int) (v1 : Int)
  (h1 : 1 ≤ v1 ∧ v1 ≤ 100)
  (h2 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (h3 : -1000 ≤ x3 ∧ x3 ≤ 1000) :
  solve_race x1 x1 x3 v1 v1 = "Draw" :=
  sorry
-- </vc-theorems>
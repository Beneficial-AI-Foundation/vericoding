-- <vc-helpers>
-- </vc-helpers>

def Board := Nat × Nat

def solve_football_masterchef (boards: List Board) : String := sorry

theorem valid_result (boards: List Board) 
  (h: boards.length ≥ 1 ∧ boards.length ≤ 100) 
  (h2: ∀ b ∈ boards, b.1 ≥ 1 ∧ b.1 ≤ 1000 ∧ b.2 ≥ 1 ∧ b.2 ≤ 1000) :
  solve_football_masterchef boards = "MasterChef" ∨ 
  solve_football_masterchef boards = "Football" := sorry

theorem deterministic (boards: List Board)  
  (h: boards.length ≥ 1) :
  solve_football_masterchef boards = solve_football_masterchef boards := sorry

theorem two_by_two_boards (boards: List Board)
  (h: boards.length ≥ 1)
  (h2: ∀ b ∈ boards, b.1 = 2 ∧ b.2 = 2) :
  solve_football_masterchef boards = (if boards.length % 2 = 0 then "Football" else "MasterChef") := sorry

/-
info: 'MasterChef'
-/
-- #guard_msgs in
-- #eval solve_football_masterchef [(2, 2)]

/-
info: 'Football'
-/
-- #guard_msgs in
-- #eval solve_football_masterchef [(2, 3), (3, 2)]

/-
info: 'Football'
-/
-- #guard_msgs in
-- #eval solve_football_masterchef [(4, 4)]

-- Apps difficulty: interview
-- Assurance level: unguarded
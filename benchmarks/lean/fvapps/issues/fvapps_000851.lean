-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem result_validity 
  (N : Nat) (Z1 Z2 : Int) (A : List Int)
  (h1 : N > 0) (h2 : N ≤ 100)
  (h3 : Z1 ≥ -1000) (h4 : Z1 ≤ 1000)
  (h5 : Z2 ≥ -1000) (h6 : Z2 ≤ 1000)
  (h7 : ∀ a ∈ A, a ≥ -1000 ∧ a ≤ 1000)
  (h8 : A.length ≥ 1) (h9 : A.length ≤ 100) :
  let result := solve_game N Z1 Z2 A
  result = 0 ∨ result = 1 ∨ result = 2 := sorry

-- Property: Result should be 1 if target is immediately reachable

theorem immediate_win
  (N : Nat) (Z : Int) (A : List Int) (a : Int)
  (h1 : N > 0) (h2 : N ≤ 100)
  (h3 : Z ≥ -1000) (h4 : Z ≤ 1000)
  (h5 : a ∈ A)
  (h6 : A.length ≥ 1) (h7 : A.length ≤ 100)
  (h8 : Int.natAbs a = Int.natAbs Z) :
  solve_game N Z (Z + 1) [a] = 1 := sorry

-- Property: Result should be symmetric for negated inputs

theorem negation_symmetry
  (N : Nat) (Z1 Z2 : Int) (A : List Int)
  (h1 : N > 0) (h2 : N ≤ 100)
  (h3 : Z1 ≥ -1000) (h4 : Z1 ≤ 1000)
  (h5 : Z2 ≥ -1000) (h6 : Z2 ≤ 1000)
  (h7 : ∀ a ∈ A, a ≥ -1000 ∧ a ≤ 1000)
  (h8 : A.length ≥ 1) (h9 : A.length ≤ 100) :
  solve_game N Z1 Z2 A = solve_game N (-Z1) (-Z2) (A.map (·*(-1))) := sorry

-- Property: Single number case should be deterministic

theorem single_number
  (num Z1 Z2 : Int)
  (h1 : num ≥ -1000) (h2 : num ≤ 1000)
  (h3 : Z1 ≥ -1000) (h4 : Z1 ≤ 1000)
  (h5 : Z2 ≥ -1000) (h6 : Z2 ≤ 1000) :
  let result := solve_game 1 Z1 Z2 [num]
  (Int.natAbs num = Int.natAbs Z1 ∨ Int.natAbs num = Int.natAbs Z2) → result = 1 ∧
  ¬(Int.natAbs num = Int.natAbs Z1 ∨ Int.natAbs num = Int.natAbs Z2) → (result = 0 ∨ result = 2) := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_game 2 6 4 [-4, 10]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_game 1 1 -1 [2]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_game 2 0 7 [3, 4]
-- </vc-theorems>
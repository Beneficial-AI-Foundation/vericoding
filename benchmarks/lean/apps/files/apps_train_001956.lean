-- <vc-helpers>
-- </vc-helpers>

def solve_photo_problem (n a b t : Nat) (orientations : String) : Nat := sorry

theorem photo_problem_result_bounds 
  (n a b t : Nat) (orientations : String) 
  (h1: n ≥ 1) (h2: n ≤ 100)
  (h3: a ≤ 100) (h4: b ≤ 100) (h5: t ≤ 1000)
  (h6: orientations.length = n) :
  let result := solve_photo_problem n a b t orientations
  0 ≤ result ∧ result ≤ n := sorry

theorem photo_problem_n_equals_one
  (a b t : Nat) (orientations : String)
  (h1: orientations.length = 1) :
  let result := solve_photo_problem 1 a b t orientations
  result = 0 ∨ result = 1 := sorry

theorem photo_problem_zero_cost
  (n : Nat) (orientations : String)
  (h1: n ≥ 1) (h2: n ≤ 100)
  (h3: orientations = String.mk (List.replicate n 'w')) :
  solve_photo_problem n 0 0 1000 orientations = n := sorry

theorem photo_problem_zero_time
  (n a b : Nat) (orientations : String)
  (h1: n ≥ 1) (h2: n ≤ 100)
  (h3: a ≥ 1) (h4: a ≤ 100)
  (h5: b ≥ 1) (h6: b ≤ 100)
  (h7: orientations = String.mk (List.replicate n 'w')) :
  let result := solve_photo_problem n a b 0 orientations
  result = 0 ∨ result = 1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_photo_problem 4 2 3 10 "wwhw"

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_photo_problem 5 2 4 13 "hhwhh"

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_photo_problem 3 1 100 10 "whw"

-- Apps difficulty: competition
-- Assurance level: unguarded
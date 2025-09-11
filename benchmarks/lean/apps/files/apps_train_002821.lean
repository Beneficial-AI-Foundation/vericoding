-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_eq (eq: List (List Int)) : List Int := sorry

def matrixMultiply (A: List (List Int)) (x: List Int) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_eq_dimensions {eq: List (List Int)} (h1: eq.length = 3) 
  (h2: ∀ row ∈ eq, row.length = 4) :
  let solution := solve_eq eq
  -- Solution has length 3
  solution.length = 3 ∧ 
  -- Solution contains only integers
  (∀ x ∈ solution, ∃ n: Int, x = n) ∧
  -- Solution satisfies original equations (Ax = b)
  let A := eq.map (λ row => row.take 3)
  let b := eq.map (λ row => row.get! 3)
  matrixMultiply A solution = b := sorry

/-
info: [1, 4, -2]
-/
-- #guard_msgs in
-- #eval solve_eq [[4, -3, 1, -10], [2, 1, 3, 0], [-1, 2, -5, 17]]

/-
info: [-1, 6, 2]
-/
-- #guard_msgs in
-- #eval solve_eq [[2, 1, 3, 10], [-3, -2, 7, 5], [3, 3, -4, 7]]

/-
info: [3, -1, 2]
-/
-- #guard_msgs in
-- #eval solve_eq [[3, 2, 0, 7], [-4, 0, 3, -6], [0, -2, -6, -10]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
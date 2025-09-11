-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix (α : Type) := List (List α)

def score_matrix (matrix : Matrix Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem score_matrix_single_element
  (x : Int) :
  score_matrix [[x]] = x := sorry

theorem score_matrix_zero
  (n : Nat)
  (h : n > 0) :
  score_matrix (List.replicate n (List.replicate n 0)) = 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval score_matrix [[1, 2, 3], [-3, -2, 1], [3, -1, 2]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval score_matrix [[1, -1], [-1, 1]]

/-
info: 5
-/
-- #guard_msgs in
-- #eval score_matrix [[5]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
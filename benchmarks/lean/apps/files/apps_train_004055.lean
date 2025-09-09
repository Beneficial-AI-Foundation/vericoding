-- <vc-helpers>
-- </vc-helpers>

def diagonal (matrix : List (List Int)) : String := sorry

theorem diagonal_2x2_property (m00 m01 m10 m11 : Int) : 
  let principal := m00 + m11
  let secondary := m01 + m10
  let matrix := [[m00, m01], [m10, m11]]
  diagonal matrix = "Principal Diagonal win!" → principal > secondary ∧
  diagonal matrix = "Secondary Diagonal win!" → secondary > principal ∧
  diagonal matrix = "Draw!" → principal = secondary := by sorry

theorem diagonal_identity_matrix_property (n : Nat) :
  n > 1 →
  let matrix := List.map (fun i => List.map (fun j => if i = j then 1 else 0) (List.range n)) (List.range n)
  diagonal matrix = "Principal Diagonal win!" := by sorry

theorem diagonal_simple_cases :
  diagonal [[5]] = "Draw!" ∧
  diagonal [[2,1],[1,3]] = "Principal Diagonal win!" := by sorry

/-
info: 'Secondary Diagonal win!'
-/
-- #guard_msgs in
-- #eval diagonal [[2, 2, 2], [4, 2, 6], [8, 8, 2]]

/-
info: 'Draw!'
-/
-- #guard_msgs in
-- #eval diagonal [[1, 2, 3], [4, 5, 6], [7, 8, 9]]

/-
info: 'Principal Diagonal win!'
-/
-- #guard_msgs in
-- #eval diagonal [[7, 2, 2], [4, 2, 6], [1, 8, 1]]

-- Apps difficulty: introductory
-- Assurance level: unguarded
-- <vc-preamble>
def identityMatrix (n : Nat) : Matrix n Float := sorry
def zeroMatrix (n : Nat) : Matrix n Float := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculateMatrixDeterminant {n : Nat} (matrix : Matrix n Float) : Float := sorry
def transpose {n : Nat} (matrix : Matrix n Float) : Matrix n Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identity_matrix_det {n : Nat} (h : n > 0) : 
  calculateMatrixDeterminant (identityMatrix n) = 1 := sorry

theorem zero_matrix_det {n : Nat} (h : n > 0) :
  calculateMatrixDeterminant (zeroMatrix n) = 0 := sorry

theorem det_2x2_formula (matrix : Matrix 2 Float) (h : matrix.data.length = 2) :
  calculateMatrixDeterminant matrix = 
    let rows := matrix.data
    let r0 := rows[0]!
    let r1 := rows[1]!
    r0[0]! * r1[1]! - r0[1]! * r1[0]! := sorry

theorem det_transpose_eq {n : Nat} (matrix : Matrix n Float) :
  calculateMatrixDeterminant (transpose matrix) = 
    calculateMatrixDeterminant matrix := sorry

/-
info: 0.0
-/
-- #guard_msgs in
-- #eval calculate_matrix_determinant [[1.1, 1.1], [1.1, 1.1]]

/-
info: -3.0
-/
-- #guard_msgs in
-- #eval calculate_matrix_determinant [[1, 2], [2, 1]]

/-
info: 0.0
-/
-- #guard_msgs in
-- #eval calculate_matrix_determinant [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
-- </vc-theorems>
-- <vc-preamble>
def Matrix := List (List Nat)

def different_squares : Matrix → Nat := sorry

def rotateMatrix (m : Matrix) : Matrix := sorry

def isValidMatrix (m : Matrix) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isAllValue (m : Matrix) (v : Nat) : Bool := sorry

-- Number of different squares is always positive and has an upper bound
-- </vc-definitions>

-- <vc-theorems>
theorem different_squares_bounds (m : Matrix) :
  isValidMatrix m → 
  1 ≤ different_squares m ∧ 
  different_squares m ≤ (m.length - 1) * ((m.head!).length - 1) :=
sorry

-- A matrix filled with same value has exactly 1 unique square

theorem same_value_matrix_one_square (m : Matrix) (v : Nat) : 
  isValidMatrix m →
  isAllValue m v →
  different_squares m = 1 :=
sorry

-- Rotating a matrix preserves number of unique squares 

theorem different_squares_rotation_invariant (m : Matrix) :
  isValidMatrix m →
  different_squares m = different_squares (rotateMatrix m) :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval different_squares [[1, 2, 1], [2, 2, 2], [2, 2, 2], [1, 2, 3], [2, 2, 1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval different_squares [[1, 1], [1, 1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval different_squares [[9, 9, 9], [9, 9, 9], [9, 9, 9]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded
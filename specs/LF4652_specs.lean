-- <vc-preamble>
def Matrix := List (List Nat)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def different_squares : Matrix → Nat :=
sorry

def rotateMatrix (m : Matrix) : Matrix :=
sorry

def isValidMatrix (m : Matrix) : Bool :=
sorry

def isAllValue (m : Matrix) (v : Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem different_squares_bounds (m : Matrix) :
  isValidMatrix m →
  1 ≤ different_squares m ∧
  different_squares m ≤ (m.length - 1) * ((m.head!).length - 1) :=
sorry

theorem same_value_matrix_one_square (m : Matrix) (v : Nat) :
  isValidMatrix m →
  isAllValue m v →
  different_squares m = 1 :=
sorry

theorem different_squares_rotation_invariant (m : Matrix) :
  isValidMatrix m →
  different_squares m = different_squares (rotateMatrix m) :=
sorry
-- </vc-theorems>
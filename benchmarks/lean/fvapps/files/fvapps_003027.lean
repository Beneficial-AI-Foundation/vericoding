-- <vc-preamble>
def Matrix (α : Type) [BEq α] := List (List α)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_matrix {α : Type} [BEq α] (m : Matrix α) : Bool :=
sorry

def rotate_against_clockwise {α : Type} [BEq α] (m : Matrix α) (times : Nat) : Matrix α :=
sorry

def get_matrix_dimensions {α : Type} [BEq α] (m : Matrix α) : Nat × Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dimensions_preserved {α : Type} [BEq α] (m : Matrix α) :
  is_valid_matrix m →
  let dims := get_matrix_dimensions m
  get_matrix_dimensions (rotate_against_clockwise m 1) = dims :=
sorry

theorem rotation_modulo {α : Type} [BEq α] (m : Matrix α) (times : Nat) :
  is_valid_matrix m →
  rotate_against_clockwise m times = rotate_against_clockwise m (times % 4) :=
sorry

theorem four_rotations_identity {α : Type} [BEq α] (m : Matrix α) :
  is_valid_matrix m →
  rotate_against_clockwise m 4 = m :=
sorry

theorem single_column_dimensions {α : Type} [BEq α] (m : Matrix α) :
  is_valid_matrix m →
  (∀ (row : List α), List.elem row m → List.length row = 1) →
  let rotated := rotate_against_clockwise m 1
  List.length rotated = List.length (List.head! m) ∧
  ∀ (row : List α), List.elem row rotated → List.length row = List.length m :=
sorry
-- </vc-theorems>
-- <vc-preamble>
def distance (p1 p2 : Point) : Int :=
  (p1.x - p2.x) * (p1.x - p2.x) + (p1.y - p2.y) * (p1.y - p2.y)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validSquare (p1 p2 p3 p4 : Point) : Bool :=
  sorry

-- If validSquare returns true, then fundamental properties of a square hold
-- </vc-definitions>

-- <vc-theorems>
theorem valid_square_properties (p1 p2 p3 p4 : Point) :
  validSquare p1 p2 p3 p4 = true →
  ∃ side diag : Int,
    -- All sides have equal length
    (distance p1 p2 = side ∧
     distance p2 p3 = side ∧
     distance p3 p4 = side ∧
     distance p4 p1 = side) ∧
    -- Both diagonals have equal length
    (distance p1 p3 = diag ∧
     distance p2 p4 = diag) ∧
    -- Diagonals are longer than sides
    diag > side ∧
    -- Side length is positive
    side > 0 :=
  sorry

-- Four identical points cannot form a valid square

theorem degenerate_case (p : Point) :
  validSquare p p p p = false :=
  sorry

-- Unit square is valid

theorem unit_square_valid :
  validSquare ⟨0,0⟩ ⟨1,0⟩ ⟨1,1⟩ ⟨0,1⟩ = true :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval validSquare [0, 0] [1, 1] [1, 0] [0, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval validSquare [0, 0] [2, 0] [2, 1] [0, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval validSquare [0, 0] [0, 0] [0, 0] [0, 0]
-- </vc-theorems>
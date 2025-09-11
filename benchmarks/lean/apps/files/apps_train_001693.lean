-- <vc-preamble>
def mouse_path (s : String) : Option Nat := sorry
def check_corner (orientations : List Char) : Bool := sorry

def check_intersect (rectas : List ((Int × Int) × (Int × Int))) : Bool := sorry
def calc_area (points : List (Int × Int)) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def add_point (direction : Char) (distance : Nat) (points : List (Int × Int)) : List (Int × Int) := sorry

theorem mouse_path_returns_none_or_natural (s : String) : 
  match mouse_path s with
  | none => True
  | some n => n ≥ 0
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_corner_single_orientation {o : Char} (orientations : List Char) :
  (∀ x ∈ orientations, x = o) → check_corner orientations = false := sorry

theorem check_intersect_symmetry (rectas : List ((Int × Int) × (Int × Int))) :
  check_intersect rectas = check_intersect rectas.reverse := sorry

theorem calc_area_nonnegative (points : List (Int × Int)) :
  calc_area points ≥ 0 := sorry

theorem add_point_preserves_coordinate (direction : Char) (distance : Nat) (points : List (Int × Int)) :
  let newPoints := add_point direction distance [(0,0)]
  (direction = 'N' ∨ direction = 'S') →
    (newPoints.get! 0).1 = (newPoints.get! 1).1 ∧
  (direction = 'E' ∨ direction = 'O') →
    (newPoints.get! 0).2 = (newPoints.get! 1).2
  := sorry

/-
info: 49
-/
-- #guard_msgs in
-- #eval mouse_path "4R2L1R5R9R4R4L3"

/-
info: None
-/
-- #guard_msgs in
-- #eval mouse_path "4R2L1R5"

/-
info: None
-/
-- #guard_msgs in
-- #eval mouse_path "2R2R2L2L"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded
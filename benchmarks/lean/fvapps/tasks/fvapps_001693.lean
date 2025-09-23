-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mouse_path (s : String) : Option Nat :=
sorry

def check_corner (orientations : List Char) : Bool :=
sorry

def check_intersect (rectas : List ((Int × Int) × (Int × Int))) : Bool :=
sorry

def calc_area (points : List (Int × Int)) : Nat :=
sorry

def add_point (direction : Char) (distance : Nat) (points : List (Int × Int)) : List (Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mouse_path_returns_none_or_natural (s : String) :
  match mouse_path s with
  | none => True
  | some n => n ≥ 0
  :=
sorry

theorem check_corner_single_orientation {o : Char} (orientations : List Char) :
  (∀ x ∈ orientations, x = o) → check_corner orientations = false :=
sorry

theorem check_intersect_symmetry (rectas : List ((Int × Int) × (Int × Int))) :
  check_intersect rectas = check_intersect rectas.reverse :=
sorry

theorem calc_area_nonnegative (points : List (Int × Int)) :
  calc_area points ≥ 0 :=
sorry

theorem add_point_preserves_coordinate (direction : Char) (distance : Nat) (points : List (Int × Int)) :
  let newPoints := add_point direction distance [(0,0)]
  (direction = 'N' ∨ direction = 'S') →
    (newPoints.get! 0).1 = (newPoints.get! 1).1 ∧
  (direction = 'E' ∨ direction = 'O') →
    (newPoints.get! 0).2 = (newPoints.get! 1).2
  :=
sorry
-- </vc-theorems>
-- <vc-preamble>
def Point := Int × Int

def Rectangle := List Point
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_rectangle_characteristics (points : Rectangle) : Float × Float × Float × Float × Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def length (points : Rectangle) : Float :=
  let (l, _, _, _, _) := calculate_rectangle_characteristics points
  l

def width (points : Rectangle) : Float :=
  let (_, w, _, _, _) := calculate_rectangle_characteristics points
  w

def area (points : Rectangle) : Float :=
  let (_, _, a, _, _) := calculate_rectangle_characteristics points
  a

def perimeter (points : Rectangle) : Float :=
  let (_, _, _, p, _) := calculate_rectangle_characteristics points
  p

def diagonal (points : Rectangle) : Float :=
  let (_, _, _, _, d) := calculate_rectangle_characteristics points
  d

theorem length_positive (points : Rectangle) :
  length points > 0 :=
sorry

theorem width_positive (points : Rectangle) :
  width points > 0 :=
sorry

theorem area_is_length_times_width (points : Rectangle) :
  area points = length points * width points :=
sorry

theorem perimeter_formula (points : Rectangle) :
  perimeter points = 2 * (length points + width points) :=
sorry

theorem diagonal_formula (points : Rectangle) :
  diagonal points = Float.sqrt (length points * length points + width points * width points) :=
sorry

theorem diagonal_larger_than_sides (points : Rectangle) :
  diagonal points > length points ∧ diagonal points > width points :=
sorry

theorem measurements_match_points (points : Rectangle) (h : points.length = 4) :
  ∃ x1 x2 y1 y2 : Int,
    (x2 > x1 ∧ y2 > y1) ∧
    points = [(x1, y1), (x1, y2), (x2, y1), (x2, y2)] ∧
    length points = Float.ofInt (x2 - x1) ∧
    width points = Float.ofInt (y2 - y1) :=
sorry
-- </vc-theorems>
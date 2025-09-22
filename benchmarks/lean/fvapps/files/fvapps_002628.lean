-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def length_of_line (coords : List (List Int)) : String :=
sorry

def string_to_float (s : String) : Float :=
sorry

def int_to_float (i : Int) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_matches_pythagorean
  (coords : List (List Int))
  (x1 y1 x2 y2 : Int)
  (h1 : coords.length = 2)
  (h2 : coords[0]!.length = 2)
  (h3 : coords[1]!.length = 2)
  (h4 : coords[0]![0]! = x1)
  (h5 : coords[0]![1]! = y1)
  (h6 : coords[1]![0]! = x2)
  (h7 : coords[1]![1]! = y2) :
  let result := string_to_float (length_of_line coords)
  let expected := Float.sqrt (int_to_float ((x2 - x1) ^ 2 + (y2 - y1) ^ 2))
  Float.abs (result - expected) < 0.01 :=
sorry

theorem length_commutative
  (coords : List (List Int))
  (h1 : coords.length = 2)
  (h2 : coords[0]!.length = 2)
  (h3 : coords[1]!.length = 2) :
  length_of_line coords = length_of_line [coords[1]!, coords[0]!] :=
sorry

theorem same_point_zero
  (coords : List (List Int))
  (h1 : coords.length = 2)
  (h2 : coords[0]!.length = 2) :
  length_of_line [coords[0]!, coords[0]!] = "0.00" :=
sorry

theorem triangle_inequality
  (coords : List (List Int))
  (x1 y1 x2 y2 : Int)
  (h1 : coords.length = 2)
  (h2 : coords[0]!.length = 2)
  (h3 : coords[1]!.length = 2)
  (h4 : coords[0]![0]! = x1)
  (h5 : coords[0]![1]! = y1)
  (h6 : coords[1]![0]! = x2)
  (h7 : coords[1]![1]! = y2) :
  let mx := (x1 + x2) / 2
  let my := (y1 + y2) / 2
  let midpoint := [mx, my]
  let result := string_to_float (length_of_line coords)
  let via_mid := string_to_float (length_of_line [coords[0]!, midpoint]) +
                 string_to_float (length_of_line [midpoint, coords[1]!])
  result ≤ via_mid + 0.01 :=
sorry
-- </vc-theorems>
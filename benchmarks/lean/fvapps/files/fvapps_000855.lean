-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Float.ofString? (s: String) : Option Float :=
sorry

def calculate_donut_areas (radii : List Int) : List String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
def Float.ofString! (s: String) : Float := (Float.ofString? s).get!

theorem calculate_donut_areas_length_match (radii : List Int) :
  (calculate_donut_areas radii).length = radii.length :=
sorry

theorem calculate_donut_areas_decimal_format (radii : List Int) (result : String) :
  result ∈ calculate_donut_areas radii →
  (∃ n d : String, result = n ++ "." ++ d ∧ d.length = 2) :=
sorry

theorem calculate_donut_areas_accuracy (radius : Int) :
  let area := calculate_donut_areas [radius]
  let expected := (Float.ofInt (radius * radius)) * 3.14
  let actual := Float.ofString! area.head!
  (actual - expected).abs < 0.01 :=
sorry

theorem calculate_donut_areas_negative_valid (radii : List Int)
  (h : ∀ r ∈ radii, r < 0) :
  (calculate_donut_areas radii).length = radii.length :=
sorry
-- </vc-theorems>
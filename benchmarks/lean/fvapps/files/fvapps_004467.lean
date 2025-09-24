-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def convert_temp (temp : Float) (from_scale : String) (to_scale : String) : Int :=
  sorry

def round (x : Float) : Int :=
  sorry

def int_to_float (n : Int) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem convert_temp_identity {temp : Float} {scale : String}
  (h1 : -1000 ≤ temp) (h2 : temp ≤ 1000) :
  convert_temp temp scale scale = round temp := by
  sorry

theorem convert_temp_returns_int {temp : Float} {from_scale to_scale : String}
  (h1 : -1000 ≤ temp) (h2 : temp ≤ 1000) :
  ∃ n : Int, convert_temp temp from_scale to_scale = n := by
  sorry

theorem convert_temp_kelvin_roundtrip {temp : Float} {scale : String}
  (h1 : -1000 ≤ temp) (h2 : temp ≤ 1000) (h3 : scale ≠ "K") :
  let kelvin := int_to_float (convert_temp temp scale "K")
  let back := convert_temp kelvin "K" scale
  (back - round temp) ≤ 2 ∧ (round temp - back) ≤ 2 := by
  sorry
-- </vc-theorems>
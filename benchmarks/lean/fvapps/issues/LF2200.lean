-- <vc-preamble>
def Water.subtract (w : Water) (v : Float) : Water :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Water.add (w1 w2 : Water) : Water :=
  sorry

instance : LE Water where
  le := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem water_reflexivity (temp vol : Float) (h1 : temp > -1000) (h2 : temp < 1000) 
    (h3 : vol > 0.1) (h4 : vol < 1000) :
  let w := { temp := temp, volume := vol : Water }
  w ≤ w :=
sorry

theorem water_antisymmetry (temp1 vol1 temp2 vol2 : Float)
    (h1 : temp1 > -1000) (h2 : temp1 < 1000) (h3 : vol1 > 0.1) (h4 : vol1 < 1000)
    (h5 : temp2 > -1000) (h6 : temp2 < 1000) (h7 : vol2 > 0.1) (h8 : vol2 < 1000) :
  let w1 := { temp := temp1, volume := vol1 : Water }
  let w2 := { temp := temp2, volume := vol2 : Water }
  w1 ≤ w2 → w2 ≤ w1 → w1.temp_vol/w1.volume = w2.temp_vol/w2.volume :=
sorry

theorem water_subtract_preserves_temp (temp vol subtract : Float)
    (h1 : temp > -1000) (h2 : temp < 1000)
    (h3 : vol > 0.1) (h4 : vol < 1000)
    (h5 : subtract > 0.1) (h6 : subtract < 1000)
    (h7 : subtract < vol) :
  let w := { temp := temp, volume := vol : Water }
  let w' := w.subtract subtract
  w'.volume = vol - subtract ∧ w'.temp_vol/w'.volume = temp :=
sorry

theorem water_add_properties (temp1 vol1 temp2 vol2 : Float)
    (h1 : temp1 > -1000) (h2 : temp1 < 1000) (h3 : vol1 > 0.1) (h4 : vol1 < 1000)
    (h5 : temp2 > -1000) (h6 : temp2 < 1000) (h7 : vol2 > 0.1) (h8 : vol2 < 1000) :
  let w1 := { temp := temp1, volume := vol1 : Water }
  let w2 := { temp := temp2, volume := vol2 : Water }
  let w' := w1.add w2
  w'.volume = vol1 + vol2 ∧ w'.temp_vol = temp1 * vol1 + temp2 * vol2 :=
sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_pressure (m1 m2 M1 M2 V T : Float) : Float := sorry

theorem pressure_positive (m1 m2 M1 M2 V T : Float)
  (h1 : m1 > 0.1) (h2 : m1 < 100)
  (h3 : m2 > 0.1) (h4 : m2 < 100) 
  (h5 : M1 > 1) (h6 : M1 < 200)
  (h7 : M2 > 1) (h8 : M2 < 200)
  (h9 : V > 0.1) (h10 : V < 100)
  (h11 : T > -50) (h12 : T < 200) :
  calculate_pressure m1 m2 M1 M2 V T > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pressure_mass_linear (m1 m2 M1 M2 V T : Float)
  (h1 : m1 > 0.1) (h2 : m1 < 100)
  (h3 : m2 > 0.1) (h4 : m2 < 100) 
  (h5 : M1 > 1) (h6 : M1 < 200)
  (h7 : M2 > 1) (h8 : M2 < 200)
  (h9 : V > 0.1) (h10 : V < 100)
  (h11 : T > -50) (h12 : T < 200) :
  calculate_pressure (2*m1) (2*m2) M1 M2 V T = 2 * calculate_pressure m1 m2 M1 M2 V T := sorry

theorem pressure_volume_inverse (m1 m2 M1 M2 V T : Float) 
  (h1 : m1 > 0.1) (h2 : m1 < 100)
  (h3 : m2 > 0.1) (h4 : m2 < 100)
  (h5 : M1 > 1) (h6 : M1 < 200) 
  (h7 : M2 > 1) (h8 : M2 < 200)
  (h9 : V > 0.1) (h10 : V < 100)
  (h11 : T > -50) (h12 : T < 200) :
  calculate_pressure m1 m2 M1 M2 (V/2) T = 2 * calculate_pressure m1 m2 M1 M2 V T := sorry

theorem pressure_temp_proportional (m1 m2 M1 M2 V T : Float)
  (h1 : m1 > 0.1) (h2 : m1 < 100)
  (h3 : m2 > 0.1) (h4 : m2 < 100)
  (h5 : M1 > 1) (h6 : M1 < 200)
  (h7 : M2 > 1) (h8 : M2 < 200) 
  (h9 : V > 0.1) (h10 : V < 100)
  (h11 : T > -50) (h12 : T < 200) :
  calculate_pressure m1 m2 M1 M2 V (T + (T + 273.15)) = 2 * calculate_pressure m1 m2 M1 M2 V T := sorry

theorem same_gas_equivalent (m M V T : Float)
  (h1 : m > 0.1) (h2 : m < 100)
  (h3 : M > 1) (h4 : M < 200)
  (h5 : V > 0.1) (h6 : V < 100)
  (h7 : T > -50) (h8 : T < 200) :
  calculate_pressure m m M M V T = calculate_pressure (2*m) 0 M M V T := sorry
-- </vc-theorems>
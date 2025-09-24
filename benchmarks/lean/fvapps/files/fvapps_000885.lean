-- <vc-preamble>
def Scale := String
def C : Scale := "C"

def TS : Scale := "TS"

instance : DecidableEq Scale := 
  fun x y => match x, y with
  | s1, s2 => String.decEq s1 s2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_scale_plays (scale_type : Scale) (octaves : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_scale_plays_positive 
  (scale_type : Scale)
  (octaves : Nat)
  (h1 : scale_type = C ∨ scale_type = TS)
  (h2 : octaves ≥ 1)
  (h3 : octaves ≤ 100) :
  calculate_scale_plays scale_type octaves > 0 :=
sorry

theorem calculate_scale_plays_formula 
  (scale_type : Scale)
  (octaves : Nat)
  (h1 : scale_type = C ∨ scale_type = TS)
  (h2 : octaves ≥ 1)
  (h3 : octaves ≤ 100) :
  calculate_scale_plays scale_type octaves = 
    (if scale_type = C then 7 else 11) * octaves - 1 :=
sorry

theorem calculate_scale_plays_invalid
  (scale_type : Scale)
  (octaves : Nat)  
  (h : scale_type ≠ C ∧ scale_type ≠ TS) :
  ¬∃ (result : Nat), calculate_scale_plays scale_type octaves = result :=
sorry
-- </vc-theorems>
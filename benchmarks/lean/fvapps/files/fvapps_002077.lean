-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Int) : Int :=
sorry

def calc_fraction (n : Int) : Int × Int :=
sorry

def fraction_to_str (frac : Int × Int) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calc_fraction_valid_output {n : Int} (h : n ≥ 2) :
  let (num, den) := calc_fraction n
  den > 0 ∧ gcd num.natAbs den.natAbs = 1 :=
sorry

theorem fraction_to_str_format {n : Int} (h : n ≥ 2) :
  let frac := calc_fraction n
  let str := fraction_to_str frac
  ∃ num den : String,
    str = num ++ "/" ++ den ∧
    (frac.1 = String.toInt! num) ∧
    (frac.2 = String.toInt! den) :=
sorry

theorem gcd_properties {a b : Int} (ha : a > 0) (hb : b > 0) :
  let g := gcd a b
  g > 0 ∧ a % g = 0 ∧ b % g = 0 :=
sorry

theorem calc_fraction_two :
  calc_fraction 2 = (1, 6) :=
sorry
-- </vc-theorems>
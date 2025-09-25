-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def bulbSwitch (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bulb_switch_nonnegative (n : Int) (h : n ≥ 0) : 
  let result := bulbSwitch n
  result ≥ 0 ∧ result ≤ n :=
  sorry

theorem bulb_switch_negative (n : Int) (h : n < 0) :
  bulbSwitch n = -1 :=
  sorry

theorem bulb_switch_zero :
  bulbSwitch 0 = 0 :=
  sorry
-- </vc-theorems>
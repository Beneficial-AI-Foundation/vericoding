-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def evaporator (content : Float) (evap_rate : Float) (threshold : Float) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem evaporator_positive 
  (content evap_rate threshold : Float)
  (hc : content > 0.1 ∧ content ≤ 1000)
  (he : evap_rate > 0.1 ∧ evap_rate < 99.9)
  (ht : threshold > 0.1 ∧ threshold < 99.9) :
  evaporator content evap_rate threshold > 0 := 
  sorry

theorem evaporator_higher_rate_fewer_days
  (content evap_rate threshold : Float)
  (hc : content > 0.1 ∧ content ≤ 1000)
  (he : evap_rate > 0.1 ∧ evap_rate < 98.9)
  (ht : threshold > 0.1 ∧ threshold < 99.9) :
  evaporator content (evap_rate + 1) threshold ≤ evaporator content evap_rate threshold :=
  sorry

theorem evaporator_higher_threshold_fewer_days
  (content evap_rate threshold : Float) 
  (hc : content > 0.1 ∧ content ≤ 1000)
  (he : evap_rate > 0.1 ∧ evap_rate < 99.9)
  (ht : threshold > 0.1 ∧ threshold < 98.9) :
  evaporator content evap_rate (threshold + 1) ≤ evaporator content evap_rate threshold :=
  sorry
-- </vc-theorems>
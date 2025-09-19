-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_library_fees (fee_per_day : Int) (max_fee : Int) (days_late : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fee_never_negative
  (fee_per_day : Int)
  (max_fee : Int) 
  (days_late : Int)
  (h1 : fee_per_day ≥ 0)
  (h2 : max_fee ≥ 0) :
  calculate_library_fees fee_per_day max_fee days_late ≥ 0 :=
  sorry

theorem fee_never_exceeds_max
  (fee_per_day : Int)
  (max_fee : Int)
  (days_late : Int) 
  (h1 : fee_per_day ≥ 0)
  (h2 : max_fee ≥ 0)
  (h3 : days_late ≥ 0) :
  calculate_library_fees fee_per_day max_fee days_late ≤ max_fee :=
  sorry

theorem zero_days_means_zero_fee
  (fee_per_day : Int)
  (max_fee : Int)
  (h1 : fee_per_day ≥ 0)
  (h2 : max_fee ≥ 0) :
  calculate_library_fees fee_per_day max_fee 0 = 0 :=
  sorry

theorem fee_scales_linearly
  (fee_per_day : Int)
  (max_fee : Int)
  (days_late : Int)
  (h1 : fee_per_day > 0)
  (h2 : max_fee > 0)
  (h3 : days_late > 0) :
  calculate_library_fees fee_per_day max_fee days_late = 
    min (days_late * fee_per_day) max_fee :=
  sorry
-- </vc-theorems>
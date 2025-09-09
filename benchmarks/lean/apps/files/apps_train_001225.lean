-- <vc-helpers>
-- </vc-helpers>

def calculate_library_fees (fee_per_day : Int) (max_fee : Int) (days_late : Int) : Int :=
  sorry

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

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_library_fees 0 0 0

/-
info: 9
-/
-- #guard_msgs in
-- #eval calculate_library_fees 1 10 9

/-
info: 40
-/
-- #guard_msgs in
-- #eval calculate_library_fees 2 100 20

/-
info: 30
-/
-- #guard_msgs in
-- #eval calculate_library_fees 5 30 10

/-
info: 20
-/
-- #guard_msgs in
-- #eval calculate_library_fees 10 50 2

/-
info: 15
-/
-- #guard_msgs in
-- #eval calculate_library_fees 3 15 7

-- Apps difficulty: interview
-- Assurance level: guarded
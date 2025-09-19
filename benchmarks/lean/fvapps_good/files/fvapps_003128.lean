-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_ages (sum_ages diff_ages : Int) : Option (Int × Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_ages_positive_inputs
  (sum_ages diff_ages : Int)
  (h1 : 0 ≤ sum_ages)
  (h2 : sum_ages ≤ 1000)
  (h3 : 0 ≤ diff_ages)
  (h4 : diff_ages ≤ 1000) :
  if sum_ages ≥ diff_ages then
    match get_ages sum_ages diff_ages with
    | some (older, younger) =>
      older ≥ younger ∧ younger ≥ 0
    | none => False
  else
    get_ages sum_ages diff_ages = none :=
sorry

theorem get_ages_negative_sum
  (sum_ages diff_ages : Int)
  (h : sum_ages < 0) :
  get_ages sum_ages diff_ages = none :=
sorry

theorem get_ages_negative_diff
  (sum_ages diff_ages : Int)
  (h : diff_ages < 0) :
  get_ages sum_ages diff_ages = none :=
sorry
-- </vc-theorems>
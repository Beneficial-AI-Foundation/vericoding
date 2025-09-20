-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def positive_sum (xs : List Int) : Int := sorry

theorem positive_sum_non_negative (xs : List Int) :
  positive_sum xs ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem positive_sum_equals_positive_filter_sum (xs : List Int) :
  positive_sum xs = (xs.filter (fun x => x > 0)).foldr (· + ·) 0 := sorry

theorem positive_sum_unchanged_remove_negative (xs : List Int) :
  positive_sum xs = positive_sum (xs.filter (fun x => x ≥ 0)) := sorry
-- </vc-theorems>
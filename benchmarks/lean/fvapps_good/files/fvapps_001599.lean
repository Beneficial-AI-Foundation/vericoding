-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def exp_sum (n : Int) : Int := sorry

-- Test negative numbers always return 0
-- </vc-definitions>

-- <vc-theorems>
theorem exp_sum_negative (n : Int) (h : n < 0) :
  exp_sum n = 0 := sorry

-- Test known values

theorem exp_sum_0 : exp_sum 0 = 1 := sorry
theorem exp_sum_1 : exp_sum 1 = 1 := sorry

theorem exp_sum_2 : exp_sum 2 = 2 := sorry
theorem exp_sum_3 : exp_sum 3 = 3 := sorry

theorem exp_sum_4 : exp_sum 4 = 5 := sorry
theorem exp_sum_5 : exp_sum 5 = 7 := sorry

theorem exp_sum_20 : exp_sum 20 = 627 := sorry
theorem exp_sum_30 : exp_sum 30 = 5604 := sorry

theorem exp_sum_40 : exp_sum 40 = 37338 := sorry
theorem exp_sum_43 : exp_sum 43 = 63261 := sorry

theorem exp_sum_60 : exp_sum 60 = 966467 := sorry
theorem exp_sum_70 : exp_sum 70 = 4087968 := sorry

theorem exp_sum_90 : exp_sum 90 = 56634173 := sorry
theorem exp_sum_200 : exp_sum 200 = 3972999029388 := sorry

theorem exp_sum_275 : exp_sum 275 = 1520980492851175 := sorry

-- Test unknown values error

theorem exp_sum_unknown (n : Int) 
  (h1 : n > 275 ∨ (n > 5 ∧ n ≠ 20 ∧ n ≠ 30 ∧ n ≠ 40 ∧ n ≠ 43 ∧ n ≠ 60 ∧ n ≠ 70 ∧ n ≠ 90 ∧ n ≠ 200 ∧ n ≠ 275)) :
  exp_sum n = 0 := sorry
-- </vc-theorems>
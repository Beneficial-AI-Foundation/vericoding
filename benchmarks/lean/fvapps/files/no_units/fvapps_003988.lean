-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_cubes (n : Nat) : Nat := sorry

theorem sum_cubes_positive (n : Nat) (h : n > 0) : 
  sum_cubes n > 0 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_cubes_greater_eq_n (n : Nat) (h : n > 0) :
  sum_cubes n ≥ n :=
sorry

theorem sum_cubes_strictly_increasing (n : Nat) (h : n > 0) :
  sum_cubes (n + 1) > sum_cubes n :=
sorry

theorem sum_cubes_base_case_one :
  sum_cubes 1 = 1 :=
sorry

theorem sum_cubes_base_case_two :
  sum_cubes 2 = 9 :=
sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def how_many_measurements (n : Nat) : Nat :=
  sorry

def log3ceil (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem measurements_non_negative (n : Nat) (h : n > 0) :
  how_many_measurements n ≥ 0 :=
sorry

theorem measurements_sufficient (n : Nat) (h : n > 0) :
  3^(how_many_measurements n) ≥ n :=
sorry

theorem edge_case_one :
  how_many_measurements 1 = 0 :=
sorry

theorem edge_case_two :
  how_many_measurements 2 = 1 :=
sorry

theorem edge_case_three :
  how_many_measurements 3 = 1 :=
sorry
-- </vc-theorems>
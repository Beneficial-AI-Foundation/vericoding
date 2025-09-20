-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def century (year : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem century_positive (year : Nat) (h : year > 0) :
  century year > 0 :=
sorry

theorem century_lower_bound (year : Nat) (h : year > 0) :
  (century year) * 100 - 99 ≤ year :=
sorry

theorem century_upper_bound (year : Nat) (h : year > 0) :
  (century year) * 100 ≥ year :=
sorry

theorem first_century (year : Nat) (h1 : year > 0) (h2 : year < 100) :
  century year = 1 :=
sorry

theorem century_boundaries_100 :
  century 100 = 1 :=
sorry

theorem century_boundaries_101 :
  century 101 = 2 :=
sorry

theorem century_boundaries_200 :
  century 200 = 2 :=
sorry

theorem century_boundaries_201 :
  century 201 = 3 :=
sorry
-- </vc-theorems>
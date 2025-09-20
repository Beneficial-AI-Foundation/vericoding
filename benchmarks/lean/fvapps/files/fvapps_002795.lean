-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sqrt (n : Nat) : Nat :=
  sorry

def num_of_open_lockers (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_open_lockers_is_floor_sqrt (n : Nat) :
  num_of_open_lockers n = sqrt n :=
sorry

theorem num_open_lockers_nonnegative (n : Nat) :
  num_of_open_lockers n ≥ 0 :=
sorry

theorem num_open_lockers_squared_bound (n : Nat) :
  (num_of_open_lockers n) * (num_of_open_lockers n) ≤ n :=
sorry

theorem num_open_lockers_next_squared_bound (n : Nat) :
  (num_of_open_lockers n + 1) * (num_of_open_lockers n + 1) > n :=
sorry

theorem num_open_lockers_zero :
  num_of_open_lockers 0 = 0 :=
sorry

theorem num_open_lockers_one :
  num_of_open_lockers 1 = 1 :=
sorry
-- </vc-theorems>
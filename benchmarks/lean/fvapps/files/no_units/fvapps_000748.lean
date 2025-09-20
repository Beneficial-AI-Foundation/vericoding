-- <vc-preamble>
def sum (xs : List Nat) : Nat :=
  xs.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_event_time (n : Nat) (times : List (List Nat)) : Nat := sorry

theorem min_event_time_single (times : List (List Nat))
  (h1 : times = [[1,1,1]]) :
  find_min_event_time 1 times = 3 :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_event_time_equal (times : List (List Nat))
  (h1 : times = [[5,5,5], [5,5,5]]) :
  find_min_event_time 2 times = 20 :=
sorry
-- </vc-theorems>
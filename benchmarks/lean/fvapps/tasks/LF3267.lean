-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_average (marks: List Nat) : Nat :=
sorry

def list_maximum (l: List Nat) : Nat :=
sorry

def list_minimum (l: List Nat) : Nat :=
sorry

def list_sum (l: List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem average_in_bounds {marks: List Nat} (h: marks ≠ []) :
  let avg := get_average marks
  avg ≤ list_maximum marks ∧ avg ≥ list_minimum marks :=
sorry

theorem average_equals_div_sum {marks: List Nat} (h: marks ≠ []) :
  get_average marks = list_sum marks / marks.length :=
sorry

theorem empty_list_error :
  get_average [] = get_average [] → False :=
sorry
-- </vc-theorems>
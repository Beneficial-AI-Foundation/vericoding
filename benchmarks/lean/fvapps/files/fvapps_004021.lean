-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_average (numbers : List Float) : Float :=
sorry

def sum (l : List Float) : Float :=
sorry

def minimum? (l : List Float) : Option Float :=
sorry

def maximum? (l : List Float) : Option Float :=
sorry

def sumInt (l : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem integer_list_average (numbers : List Int) :
  find_average (numbers.map Float.ofInt) =
    match numbers with
    | [] => 0
    | _  => Float.ofInt (sumInt numbers) / Float.ofInt numbers.length :=
sorry

theorem empty_list_average :
  find_average [] = 0 :=
sorry

theorem average_between_min_max (numbers : List Float) (h : numbers ≠ []) :
  match minimum? numbers, maximum? numbers with
  | some min, some max => min ≤ find_average numbers ∧ find_average numbers ≤ max
  | _, _ => True :=
sorry

theorem average_times_length_equals_sum (numbers : List Float) :
  match numbers with
  | [] => find_average numbers = 0
  | _  => find_average numbers * (Float.ofNat numbers.length) = sum numbers :=
sorry
-- </vc-theorems>
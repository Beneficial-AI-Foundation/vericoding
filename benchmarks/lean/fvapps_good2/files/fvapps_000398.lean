-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_best_value (arr : List Nat) (target : Nat) : Nat :=
  sorry

def sum_capped_vals (arr : List Nat) (cap : Nat) : Nat :=
  sorry

def list_maximum (arr : List Nat) (h : arr ≠ []) : Nat :=
  sorry

def abs (n : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_best_value_bounds {arr : List Nat} {target : Nat} (h : arr ≠ []) :
  let result := find_best_value arr target
  0 ≤ result ∧ result ≤ list_maximum arr h :=
sorry

theorem find_best_value_minimizes {arr : List Nat} {target : Nat} (h : arr ≠ []) :
  let result := find_best_value arr target
  let curr_diff := abs (sum_capped_vals arr result - target)
  let less := max 0 (result - 1)
  let more := min (list_maximum arr h) (result + 1)
  curr_diff ≤ abs (sum_capped_vals arr less - target) ∧
  curr_diff ≤ abs (sum_capped_vals arr more - target) :=
sorry

theorem find_best_value_target_one {arr : List Nat} (h : arr ≠ []) :
  let result := find_best_value arr 1
  result = 0 ∨ result = 1 :=
sorry
-- </vc-theorems>
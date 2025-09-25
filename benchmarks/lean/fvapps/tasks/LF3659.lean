-- <vc-preamble>
def sum_list : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + sum_list xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_dates (records : List (String × String)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_dates_output_format {records : List (String × String)} 
  (h : records ≠ []) : 
  let result := check_dates records;
  (result.length = 3) ∧ 
  (∀ x ∈ result, x ≥ 0) ∧
  (sum_list result = records.length) :=
sorry

theorem check_dates_empty : 
  check_dates [] = [0, 0, 0] :=
sorry

theorem check_dates_output_valid (records : List (String × String)) :
  ∀ x ∈ check_dates records, x ≥ 0 :=
sorry
-- </vc-theorems>
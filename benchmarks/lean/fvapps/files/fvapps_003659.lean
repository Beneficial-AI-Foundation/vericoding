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

/-
info: [0, 0, 0]
-/
-- #guard_msgs in
-- #eval check_dates []

/-
info: [1, 0, 0]
-/
-- #guard_msgs in
-- #eval check_dates [["2015-04-04", "2015-05-13"]]

/-
info: [0, 1, 0]
-/
-- #guard_msgs in
-- #eval check_dates [["2011-10-08", "2011-08-14"]]

/-
info: [0, 0, 1]
-/
-- #guard_msgs in
-- #eval check_dates [["2002-02-07", "2002-12-10"]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded
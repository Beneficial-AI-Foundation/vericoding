-- <vc-preamble>
def monthAbbr : Month → String
| Month.Jan => "Jan"
| Month.Feb => "Feb" 
| Month.Mar => "Mar"
| Month.Apr => "Apr"
| Month.May => "May"
| Month.Jun => "Jun"
| Month.Jul => "Jul"
| Month.Aug => "Aug"
| Month.Sep => "Sep"
| Month.Oct => "Oct"
| Month.Nov => "Nov"
| Month.Dec => "Dec"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (startYear endYear : Nat) : String × String × Nat :=
sorry

-- Theorems based on property tests
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_type (startYear endYear : Nat) : 
  let result := solve startYear endYear
  result.1 = result.1 ∧ result.2.1 = result.2.1 ∧ result.2.2 > 0 :=
sorry 

theorem solve_valid_months (startYear endYear : Nat) :
  let result := solve startYear endYear
  let months31 := [Month.Jan, Month.Mar, Month.May, Month.Jul, Month.Aug, Month.Oct, Month.Dec]
  result.1 ∈ months31.map monthAbbr ∧ 
  result.2.1 ∈ months31.map monthAbbr :=
sorry

theorem solve_count_bounds (startYear endYear : Nat) (h : endYear ≥ startYear) :
  let result := solve startYear endYear 
  let yearDiff := endYear - startYear + 1
  let maxPossible := yearDiff * 7
  0 < result.2.2 ∧ result.2.2 ≤ maxPossible :=
sorry

theorem solve_guaranteed_solution (startYear endYear : Nat) 
  (h1 : startYear ≥ 1800) (h2 : endYear ≤ 2500) (h3 : endYear ≥ startYear + 10) :
  let result := solve startYear endYear
  result.2.2 > 0 :=
sorry

/-
info: ('Jan', 'May', 5)
-/
-- #guard_msgs in
-- #eval solve 2016 2020

/-
info: ('Mar', 'Dec', 51)
-/
-- #guard_msgs in
-- #eval solve 1900 1950

/-
info: ('Aug', 'Oct', 702)
-/
-- #guard_msgs in
-- #eval solve 1800 2500
-- </vc-theorems>
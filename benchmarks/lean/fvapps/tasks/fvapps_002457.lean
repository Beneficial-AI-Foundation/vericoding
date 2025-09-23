-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_second_lowest_students (records: List (String × Float)) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_same_grade_failures 
  (records: List (String × Float))
  (h1: records.length > 0)
  (h2: ∀ x y, x ∈ records → y ∈ records → x.2 = y.2) :
  ∀ result, result ≠ find_second_lowest_students records :=
sorry

theorem multiple_second_lowest_properties
  (n: Nat)
  (h1: n ≥ 2)
  (h2: n ≤ 100)
  (records := ("A", 10.0) :: 
              (List.range n).map (fun i => ("Student" ++ toString i, 20.0)) ++
              [("Z", 30.0)]) :
  let result := find_second_lowest_students records;
  -- Result has correct length
  result.length = n
  -- All elements start with "Student"
  ∧ (∀ x, x ∈ result → x.startsWith "Student")
  -- Adjacent elements are ordered
  ∧ (∀ i, i < result.length - 1 → result[i]! ≤ result[i+1]!) :=
sorry

theorem basic_properties
  (records := [("A", 10.0), ("B", 20.0), ("C", 20.0), ("D", 30.0)]) :
  let result := find_second_lowest_students records;
  -- Correct result elements
  result = ["B", "C"]
  -- Correct length 
  ∧ result.length = 2
  -- Adjacent elements are ordered
  ∧ (∀ i, i < result.length - 1 → result[i]! ≤ result[i+1]!) :=
sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_rectangle_area (heights : List Nat) : Nat :=
  sorry

def listMaximum (l : List Nat) : Nat :=
  sorry

def listModify (l : List Nat) (i : Nat) (f : Nat → Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_rectangle_area_non_negative (heights : List Nat) :
  0 ≤ largest_rectangle_area heights :=
sorry

theorem largest_rectangle_area_upper_bound (heights : List Nat) :
  heights ≠ [] →
  largest_rectangle_area heights ≤ (List.length heights) * (listMaximum heights) :=
sorry

theorem largest_rectangle_area_at_least_max_height (heights : List Nat) :
  heights ≠ [] →
  largest_rectangle_area heights ≥ listMaximum heights :=
sorry

theorem largest_rectangle_area_empty (heights : List Nat) :
  heights = [] →
  largest_rectangle_area heights = 0 :=
sorry

theorem largest_rectangle_area_tall_column (heights : List Nat) :
  heights ≠ [] →
  let tall_height := (listMaximum heights) + 1
  let new_heights := heights ++ [tall_height]
  largest_rectangle_area new_heights ≥ tall_height :=
sorry

theorem largest_rectangle_area_monotonic (heights : List Nat) (i : Nat) :
  i < List.length heights →
  let increased := listModify heights i (· + 1)
  largest_rectangle_area increased ≥ largest_rectangle_area heights :=
sorry
-- </vc-theorems>
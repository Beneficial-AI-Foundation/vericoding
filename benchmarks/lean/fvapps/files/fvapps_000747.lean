-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_rectangle_areas (n : Nat) (numbers : List Nat) : Nat × Nat :=
sorry

def maximumTwoProduct (l : List Nat) : Nat :=
sorry

def minimumTwoProduct (l : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_rectangle_areas_ordering
  (numbers : List Nat)
  (h : numbers.length ≥ 2) :
  let (max_area, min_area) := find_rectangle_areas numbers.length numbers
  max_area ≥ min_area :=
sorry

theorem find_rectangle_areas_minimal
  (numbers : List Nat)
  (h : numbers = [1, 1]) :
  find_rectangle_areas 2 numbers = (1, 1) :=
sorry

theorem find_rectangle_areas_preserves_input
  (numbers : List Nat)
  (h : numbers.length ≥ 2) :
  let original := numbers
  let _ := find_rectangle_areas numbers.length numbers
  numbers = original :=
sorry
-- </vc-theorems>
-- <vc-preamble>
def list_sum : List Nat → Nat
  | [] => 0
  | (h :: t) => h + list_sum t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_temple_operations (n : Nat) (heights : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_temple_operations_nonnegative (n : Nat) (heights : List Nat) :
  heights.length = n →
  min_temple_operations n heights ≥ 0 :=
sorry

theorem min_temple_operations_preserves_input (n : Nat) (heights : List Nat) :
  heights.length = n →
  heights = heights :=
sorry

theorem min_temple_operations_bounded_by_sum (n : Nat) (heights : List Nat) :
  heights.length = n →
  min_temple_operations n heights ≤ list_sum heights :=
sorry

theorem min_temple_operations_perfect (heights : List Nat) :
  heights = [1,2,3,2,1] →
  min_temple_operations 5 heights = 0 :=
sorry
-- </vc-theorems>
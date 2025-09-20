-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_freq (l: List Int) : Nat :=
  sorry

def find_shortest_subarray (l : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_subarray_bounds {l : List Int} (h: l ≠ []) :
  1 ≤ find_shortest_subarray l ∧ find_shortest_subarray l ≤ l.length :=
sorry

theorem single_element_list {l : List Int} (h: l.length = 1) :
  find_shortest_subarray l = 1 :=
sorry
-- </vc-theorems>
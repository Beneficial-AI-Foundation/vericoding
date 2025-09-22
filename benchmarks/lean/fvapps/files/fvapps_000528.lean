-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Grid := List (List Char)

def count_colored_squares (grid: Grid) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_colored_squares_nonnegative (grid: Grid) 
  (h: grid.length ≥ 2) : 
  count_colored_squares grid ≥ 0 :=
  sorry

theorem count_colored_squares_upper_bound (grid: Grid)
  (h: grid.length ≥ 2) :
  let n := grid.length
  count_colored_squares grid ≤ (n-1) * (n-1) * 4 :=
  sorry
-- </vc-theorems>
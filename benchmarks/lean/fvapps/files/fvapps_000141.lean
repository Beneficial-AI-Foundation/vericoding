-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_fruit (tree : List Nat) : Nat :=
sorry

def maxSubseqLengthWithTwoTypes (tree : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_fruit_bounds {tree : List Nat} (h : tree ≠ []) :
  1 ≤ total_fruit tree ∧ total_fruit tree ≤ tree.length :=
sorry

theorem total_fruit_min_length {tree : List Nat} (h : tree.length ≥ 3) :
  total_fruit tree ≥ 2 :=
sorry
-- </vc-theorems>
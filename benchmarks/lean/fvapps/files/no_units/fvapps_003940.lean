-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (x y : Nat) : Nat := sorry

instance : ToString Nat where
  toString := sorry

/- For any valid range, the count is non-negative -/
-- </vc-definitions>

-- <vc-theorems>
theorem solve_nonneg {x y : Nat} (h : x ≤ y) : 
  solve x y ≥ 0 := sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cake_slice (n : Nat) : Nat := sorry

theorem cake_slice_positive (n : Nat) :
  cake_slice n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cake_slice_grows (n : Nat) :
  cake_slice n ≥ n + 1 := sorry 

theorem cake_slice_formula (n : Nat) :
  cake_slice n = (n * n + n + 2) / 2 := sorry

theorem cake_slice_bounded_growth (n : Nat) (h : n > 0) :
  cake_slice n ≤ cake_slice (n-1) + n := sorry
-- </vc-theorems>
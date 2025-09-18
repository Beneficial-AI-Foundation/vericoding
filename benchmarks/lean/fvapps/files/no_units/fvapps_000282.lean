-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_sum_two_no_overlap (A : List Int) (L M : Nat) : Int := sorry

theorem equal_window_sizes (A : List Int) (L : Nat) :
  2 * L ≤ A.length →
  max_sum_two_no_overlap A L L = max_sum_two_no_overlap A L L := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_sum_two_bounds (A : List Int) (L M : Nat) :
  -- Result is symmetric for L and M
  max_sum_two_no_overlap A L M = max_sum_two_no_overlap A M L := by sorry
-- </vc-theorems>
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_sixes (n : Nat) : Nat := sorry

theorem count_sixes_non_negative (n : Nat) (h : n > 0) :
  count_sixes n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_sixes_monotonic (n : Nat) (h : n > 1) :
  count_sixes n ≥ count_sixes (n-1) := sorry
-- </vc-theorems>
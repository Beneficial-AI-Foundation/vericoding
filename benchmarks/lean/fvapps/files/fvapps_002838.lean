-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def infected_zeroes (arr : List Nat) : Nat := sorry

theorem infected_zeroes_singleton_zero (arr : List Nat)
  (h : arr = [0]) :
  infected_zeroes arr = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem infected_zeroes_singleton_one (arr : List Nat)
  (h : arr = [1]) :
  infected_zeroes arr = 1 := sorry
-- </vc-theorems>
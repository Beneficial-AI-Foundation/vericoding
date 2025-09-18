-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def candles (initialCandles : Nat) (makeNew : Nat) : Nat := sorry

theorem candles_at_least_initial (initialCandles : Nat) (makeNew : Nat)
  (h1 : initialCandles ≥ 1) (h2 : makeNew ≥ 2) :
  candles initialCandles makeNew ≥ initialCandles := by sorry

/- The candles_is_nat theorem is not needed since the return type is already Nat -/
-- </vc-definitions>

-- <vc-theorems>
theorem candles_upper_bound (initialCandles : Nat) (makeNew : Nat)
  (h1 : initialCandles ≥ 1) (h2 : makeNew ≥ 2) :
  candles initialCandles makeNew ≤ initialCandles + (initialCandles - 1) / (makeNew - 1) := by sorry

theorem candles_make_new_2 (initialCandles : Nat)
  (h : initialCandles ≥ 1) :
  candles initialCandles 2 = initialCandles * 2 - 1 := by sorry

theorem candles_edge_case_min :
  candles 1 2 = 1 := by sorry

theorem candles_no_new_possible (n m : Nat)
  (h1 : n ≥ 1) (h2 : m > n) :
  candles n m = n := by sorry
-- </vc-theorems>
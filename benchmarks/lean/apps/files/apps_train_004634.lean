-- <vc-helpers>
-- </vc-helpers>

def candles (initialCandles : Nat) (makeNew : Nat) : Nat := sorry

theorem candles_at_least_initial (initialCandles : Nat) (makeNew : Nat)
  (h1 : initialCandles ≥ 1) (h2 : makeNew ≥ 2) :
  candles initialCandles makeNew ≥ initialCandles := by sorry

/- The candles_is_nat theorem is not needed since the return type is already Nat -/

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

/-
info: 9
-/
-- #guard_msgs in
-- #eval candles 5 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval candles 1 2

/-
info: 11
-/
-- #guard_msgs in
-- #eval candles 8 3

-- Apps difficulty: introductory
-- Assurance level: guarded
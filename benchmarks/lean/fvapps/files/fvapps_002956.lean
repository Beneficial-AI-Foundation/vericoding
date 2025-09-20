-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def twoDecimalPlaces (n : Float) : Float := sorry

theorem decimal_places_precision (n : Float)
  (h : ¬ n.isNaN ∧ ¬ n.isInf ∧ -1e10 ≤ n ∧ n ≤ 1e10) :
  Float.abs (n - twoDecimalPlaces n) < 0.01 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem decimal_places_bound (n : Float)  
  (h : ¬ n.isNaN ∧ ¬ n.isInf ∧ -1e10 ≤ n ∧ n ≤ 1e10) :
  ∃ k : Int, twoDecimalPlaces n = Float.ofInt k / 100 := sorry
-- </vc-theorems>
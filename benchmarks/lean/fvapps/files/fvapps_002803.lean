-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fortune (f0 : Int) (p : Float) (c0 : Int) (n : Int) (i : Float) : Bool := sorry

theorem fortune_returns_bool (f0 : Int) (p : Float) (c0 : Int) (n : Int) (i : Float)
  (h1 : f0 > 0)
  (h2 : 0 ≤ p ∧ p ≤ 100)
  (h3 : c0 ≥ 0)
  (h4 : n > 0 ∧ n ≤ 50)
  (h5 : 0 ≤ i ∧ i ≤ 100) :
  fortune f0 p c0 n i = true ∨ fortune f0 p c0 n i = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem higher_initial_improves_success (f0 : Int) (p : Float) (c0 : Int) (n : Int) (i : Float)
  (h1 : f0 > 0)
  (h2 : 0 ≤ p ∧ p ≤ 100)
  (h3 : c0 ≥ 0)
  (h4 : n > 0 ∧ n ≤ 50)
  (h5 : 0 ≤ i ∧ i ≤ 100)
  (h6 : fortune f0 p c0 n i = true) :
  fortune (2 * f0) p c0 n i = true := sorry

theorem higher_withdrawal_reduces_success (f0 : Int) (p : Float) (c0 : Int) (n : Int) (i : Float)
  (h1 : f0 > 0)
  (h2 : 0 ≤ p ∧ p ≤ 100)
  (h3 : c0 > 0)
  (h4 : n > 0 ∧ n ≤ 50)
  (h5 : 0 ≤ i ∧ i ≤ 100)
  (h6 : fortune f0 p c0 n i = false) :
  fortune f0 p (2 * c0) n i = false := sorry

theorem zero_withdrawal_succeeds (f0 : Int) (p : Float) (n : Int) (i : Float)
  (h1 : f0 > 0)
  (h2 : 0 ≤ p ∧ p ≤ 100)
  (h3 : n > 0 ∧ n ≤ 50)
  (h4 : 0 ≤ i ∧ i ≤ 100) :
  fortune f0 p 0 n i = true := sorry
-- </vc-theorems>